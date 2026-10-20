"""
UltraCalc - a feature-packed calculator built with customtkinter.

Setup:   pip install customtkinter
Run:     python main.py                    # GUI
         python main.py "2^10" "5!=120"    # one-shot, prints results
         python main.py --repl             # interactive terminal mode

Highlights
  * Safe expression engine (no eval): + - * / // mod ^ ! % () functions, constants, variables
  * Equation VALIDATOR: type  1+1=11  ->  Wrong,  5!=120  ->  Correct  (also < > <= >= and chains)
  * Live preview while you type, history (saved between runs), memory, ANS, DEG/RAD
  * Function grapher with hover trace, base/unit converters, number lab, statistics, calculus lab
  * Math Challenge game (solve it / spot right-or-wrong) with streaks

Library use (no GUI needed)
    >>> from main import Engine, calc
    >>> calc("2^10")
    1024
    >>> eng = Engine()
    >>> eng.process("x := 7").value
    7
    >>> f = eng.compile("x^2 + 1", params=("x",))
    >>> f(x=3)
    10
    >>> eng.process("1+1=11").ok
    False
"""
from __future__ import annotations

import argparse
import ast
import ctypes
import ctypes.util
import json
import math
import os
import queue
import random
import re
import shutil
import statistics
import subprocess
import sys
import threading
import time
from contextlib import contextmanager
from dataclasses import dataclass
from datetime import datetime
from decimal import ROUND_HALF_UP, Decimal, localcontext
from fractions import Fraction
from typing import Callable, Iterable, Union

try:  # the GUI is optional: the engine and CLI work without tkinter/customtkinter
    import tkinter as tk
    import tkinter.font
    from tkinter import filedialog

    import customtkinter as ctk
except ImportError:  # pragma: no cover - depends on the environment
    tk = filedialog = ctk = None

Number = Union[int, float]

# --------------------------------------------------------------------------- #
#  Constants & small helpers
# --------------------------------------------------------------------------- #
MONO = ("Consolas" if sys.platform.startswith("win")
        else "Menlo" if sys.platform == "darwin" else "DejaVu Sans Mono")
GREEN, RED = "#2FA572", "#E5484D"
TEXT = ("gray10", "gray92")
MUTED = ("gray45", "gray60")
HISTORY_FILE = os.path.join(os.path.expanduser("~"), ".ultracalc_history.json")
SETTINGS_FILE = os.path.join(os.path.expanduser("~"), ".ultracalc_settings.json")
HISTORY_LIMIT = 200          # entries kept on disk
HISTORY_SHOWN = 60           # entries shown in the sidebar
SUP = str.maketrans("0123456789", "⁰¹²³⁴⁵⁶⁷⁸⁹")

MAX_INT_BITS = 70_000        # ~21k digits; keeps every operation (and the UI) responsive
MAX_FACTORIAL = 5000
MAX_FIB = 20000
MAX_PRIME_SEARCH = 10 ** 200
FACTOR_LIMIT_PREVIEW = 10 ** 18   # factorization shown live under results
FACTOR_LIMIT_LAB = 10 ** 20       # factorization in the Number lab
LOG10_2 = math.log10(2)

CONSTS = {
    "pi": math.pi,
    "e": math.e,
    "tau": math.tau,
    "phi": (1 + 5 ** 0.5) / 2,
}

UNITS = {
    "Length": {"m": 1, "km": 1000, "cm": 0.01, "mm": 0.001, "mile": 1609.344,
               "yard": 0.9144, "foot": 0.3048, "inch": 0.0254},
    "Mass": {"kg": 1, "g": 0.001, "mg": 1e-6, "tonne": 1000, "lb": 0.45359237,
             "oz": 0.028349523125},
    "Time": {"second": 1, "minute": 60, "hour": 3600, "day": 86400, "week": 604800},
    "Data": {"bit": 0.125, "byte": 1, "KB": 1e3, "MB": 1e6, "GB": 1e9, "TB": 1e12,
             "KiB": 1024, "MiB": 1024 ** 2, "GiB": 1024 ** 3},
    "Speed": {"m/s": 1, "km/h": 1 / 3.6, "mph": 0.44704, "knot": 0.514444444},
    "Area": {"m²": 1, "km²": 1e6, "ha": 1e4, "ft²": 0.09290304, "acre": 4046.8564224},
    "Temperature": {"°C": None, "°F": None, "K": None},
}


class CalcError(Exception):
    """Any user-facing calculation problem."""


def close(a: Number, b: Number) -> bool:
    """Equality with float tolerance; exact for integers (works for huge ints too)."""
    if isinstance(a, int) and isinstance(b, int):
        return a == b
    try:
        return math.isclose(a, b, rel_tol=1e-9, abs_tol=1e-12)
    except OverflowError:  # an int too big for float vs. a float: they can't be equal
        return False


def convert_temperature(v: Number, src: str, dst: str) -> float:
    celsius = {"°C": v, "°F": (v - 32) * 5 / 9, "K": v - 273.15}[src]
    return {"°C": celsius, "°F": celsius * 9 / 5 + 32, "K": celsius + 273.15}[dst]


def convert_unit(v: Number, category: str, src: str, dst: str) -> Number:
    """Convert ``v`` between two units of one ``UNITS`` category."""
    if category == "Temperature":
        return convert_temperature(v, src, dst)
    table = UNITS[category]
    return v * table[src] / table[dst]


def strip_lhs(src: str) -> str:
    """Drop a leading 'y =' or 'f(x) =' so users can type full function definitions."""
    return re.sub(r"^\s*(?:y|f\(x\))\s*=\s*", "", src)


# --------------------------------------------------------------------------- #
#  Number theory
# --------------------------------------------------------------------------- #
def _sieve(limit):
    flags = bytearray([1]) * (limit + 1)
    flags[0:2] = b"\x00\x00"
    for i in range(2, math.isqrt(limit) + 1):
        if flags[i]:
            flags[i * i::i] = bytearray(len(flags[i * i::i]))
    return [i for i, f in enumerate(flags) if f]


SMALL_PRIMES = _sieve(1000)
_MR_BASES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)  # deterministic below 3.3e24


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    for p in _MR_BASES:
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in _MR_BASES:
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def next_prime(n: int) -> int:
    if n < 2:
        return 2
    n += 1 + (n % 2 == 1)  # next odd number
    while not is_prime(n):
        n += 2
    return n


def prev_prime(n: int) -> int | None:
    if n <= 2:
        return None
    if n == 3:
        return 2
    n -= 1 + (n % 2 == 1)  # previous odd number
    while n > 2 and not is_prime(n):
        n -= 2
    return n


def _pollard_brent(n: int) -> int:
    """Return a non-trivial factor of the odd composite ``n``."""
    rng = random.Random(n)
    while True:
        y, c, m = rng.randrange(1, n), rng.randrange(1, n), 128
        g = r = q = 1
        x = ys = y
        while g == 1:
            x = y
            for _ in range(r):
                y = (y * y + c) % n
            k = 0
            while k < r and g == 1:
                ys = y
                for _ in range(min(m, r - k)):
                    y = (y * y + c) % n
                    q = q * abs(x - y) % n
                g = math.gcd(q, n)
                k += m
            r *= 2
        if g == n:
            g = 1
            while g == 1:
                ys = (ys * ys + c) % n
                g = math.gcd(abs(x - ys), n)
        if g != n:
            return g


def factorize(n: int) -> dict[int, int]:
    """Prime factorization {prime: exponent} of |n| (trial division + Pollard-Brent)."""
    n, out = abs(n), {}
    for p in SMALL_PRIMES:
        if p * p > n:
            break
        while n % p == 0:
            out[p] = out.get(p, 0) + 1
            n //= p
    stack = [n] if n > 1 else []
    while stack:
        m = stack.pop()
        if is_prime(m):
            out[m] = out.get(m, 0) + 1
        else:
            d = _pollard_brent(m)
            stack += [d, m // d]
    return dict(sorted(out.items()))


def factor_str(f: dict[int, int]) -> str:
    return " × ".join(f"{p}{str(e).translate(SUP)}" if e > 1 else str(p)
                      for p, e in sorted(f.items()))


# --------------------------------------------------------------------------- #
#  Formatting
# --------------------------------------------------------------------------- #
def digit_count(n: int) -> int:
    """Number of decimal digits of |n| - works beyond Python's int->str limit."""
    n = abs(n)
    if n < 10 ** 18:
        return len(str(n))
    d = int((n.bit_length() - 1) * LOG10_2) + 1  # never more than one too small
    return d + 1 if n >= 10 ** d else d


def fmt(v, digits: int = 12) -> str:
    """Pretty number formatting."""
    if isinstance(v, bool):
        return str(int(v))
    if isinstance(v, int):
        d = digit_count(v)
        if d > 30:
            lead = str(abs(v) // 10 ** (d - 11))
            return f"{'-' if v < 0 else ''}{lead[0]}.{lead[1:]}e+{d - 1}"
        return str(v)
    if isinstance(v, float):
        if v.is_integer() and abs(v) < 1e15:
            return str(int(v))
        return f"{v:.{digits}g}"
    return str(v)


def insights(v: Number) -> str:
    """Small extra info shown under the result."""
    try:
        if isinstance(v, float) and v.is_integer() and abs(v) < 1e15:
            v = int(v)
        if isinstance(v, int):
            a, sign, out = abs(v), "-" if v < 0 else "", []
            d = digit_count(a)
            if d > 15:
                out.append(f"{d} digits")
            if a < 2 ** 64:
                out.append(f"bin {sign}{a:b}   hex {sign}{a:x}")
            if 2 <= a <= FACTOR_LIMIT_PREVIEW:
                out.append("prime ✨" if is_prime(a) else "= " + factor_str(factorize(a)))
            return "    ".join(out)
        fr = Fraction(v).limit_denominator(1000)
        if fr.denominator != 1 and abs(float(fr) - v) < 1e-9 * max(1, abs(v)):
            return f"≈ {fr.numerator}/{fr.denominator}    sci {v:.6e}"
        return f"sci {v:.6e}"
    except Exception:
        return ""


# --------------------------------------------------------------------------- #
#  Math functions
# --------------------------------------------------------------------------- #
def _as_int(x, what="value") -> int:
    if isinstance(x, float):
        if not x.is_integer():
            raise CalcError(f"{what} must be a whole number")
        x = int(x)
    return x


def _guard_int(v):
    """Reject integers so large that further work would freeze the app."""
    if type(v) is int and v.bit_length() > MAX_INT_BITS:
        raise CalcError("Result too large")
    return v


def _guard_log2(bits: float):
    if bits > MAX_INT_BITS:
        raise CalcError("Result too large")


def _snap(v: float) -> float:
    """Round away float noise such as sin(30°) = 0.49999999999999994."""
    return float(f"{v:.15g}")


def fact(x):
    if isinstance(x, float) and not x.is_integer():
        if x > 170:
            raise CalcError("Factorial too large")
        return math.gamma(x + 1)
    n = int(x)
    if n < 0:
        raise CalcError("Factorial of a negative integer is undefined")
    if n > MAX_FACTORIAL:
        raise CalcError(f"Factorial too large (max {MAX_FACTORIAL}!)")
    return math.factorial(n)


def fib(n):
    """n-th Fibonacci number (fast doubling)."""
    n = _as_int(n, "n")
    if not 0 <= n <= MAX_FIB:
        raise CalcError(f"fib(n) needs 0 <= n <= {MAX_FIB}")
    a, b = 0, 1
    for bit in bin(n)[2:]:
        c, d = a * (2 * b - a), a * a + b * b
        a, b = (d, c + d) if bit == "1" else (c, d)
    return a


def _round(x, n=0):
    """Round half away from zero, like a pocket calculator: round(-2.5) = -3, round(2.675, 2) = 2.68."""
    n = _as_int(n, "digits")
    if isinstance(x, int):
        if n >= 0:
            return x
        step = 10 ** -n
        q, r = divmod(abs(x), step)
        q += 2 * r >= step
        return q * step * (1 if x >= 0 else -1)
    if n > 17:
        return x
    if n < -330:
        return 0
    with localcontext() as ctx:
        ctx.prec = 400
        q = Decimal(repr(x)).quantize(Decimal(1).scaleb(-n), rounding=ROUND_HALF_UP)
    return int(q) if n <= 0 else float(q)


def _root(x, n):
    n = _as_int(n, "root degree")
    if n == 0:
        raise CalcError("Root degree cannot be 0")
    if x < 0 and n % 2 == 0:
        raise CalcError("Even root of a negative number")
    res = math.copysign(abs(x) ** (1 / n), x)
    if n > 0 and (isinstance(x, int) or x.is_integer()):
        r = round(res)
        if r ** n == x:
            return r
    return res


def _cbrt(x):
    return _root(x, 3)


def _comb(n, r):
    n, r = _as_int(n, "n"), _as_int(r, "r")
    if n < 0 or r < 0:
        raise CalcError("nCr needs n, r >= 0")
    if r > n:
        return 0
    _guard_log2((math.lgamma(n + 1) - math.lgamma(r + 1) - math.lgamma(n - r + 1)) / math.log(2))
    return math.comb(n, r)


def _perm(n, r):
    n, r = _as_int(n, "n"), _as_int(r, "r")
    if n < 0 or r < 0:
        raise CalcError("nPr needs n, r >= 0")
    if r > n:
        return 0
    _guard_log2((math.lgamma(n + 1) - math.lgamma(n - r + 1)) / math.log(2))
    return math.perm(n, r)


def _checked_prime_arg(n):
    n = _as_int(n)
    if abs(n) > MAX_PRIME_SEARCH:
        raise CalcError("Number too large for prime functions")
    return n


def _variadic(f, name, minimum=1):
    def g(*args):
        if len(args) < minimum:
            raise CalcError(f"{name}() needs at least {minimum} value{'s' if minimum > 1 else ''}")
        return f(args)
    return g


def _div(a, b):
    if b == 0:
        raise CalcError("Division by zero")
    if isinstance(a, int) and isinstance(b, int) and a % b == 0:
        return a // b
    return a / b


def _floordiv(a, b):
    if b == 0:
        raise CalcError("Division by zero")
    return a // b


def _mod(a, b):
    if b == 0:
        raise CalcError("Division by zero")
    return a % b


def _pow(a, b):
    if a == 0 and b < 0:
        raise CalcError("Division by zero")
    if a < 0 and not (isinstance(b, int) or float(b).is_integer()):
        raise CalcError("Complex results are not supported")
    if isinstance(a, int) and isinstance(b, int) and b > 0 and abs(a) > 1:
        _guard_log2(b * math.log2(abs(a)))
    return a ** b


# --------------------------------------------------------------------------- #
#  Numeric calculus (pure functions: f is any float -> float callable)
# --------------------------------------------------------------------------- #
def derivative(f: Callable[[float], float], a: float) -> float:
    """Five-point central difference; the step scales with |a|."""
    h = 1e-3 * max(1.0, abs(a))
    return (-f(a + 2 * h) + 8 * f(a + h) - 8 * f(a - h) + f(a - 2 * h)) / (12 * h)


def integrate(f: Callable[[float], float], a: float, b: float, n: int = 2000) -> float:
    """Composite Simpson's rule with ``n`` (even) intervals."""
    n += n % 2
    h = (b - a) / n
    s = f(a) + f(b) + sum((4 if i % 2 else 2) * f(a + i * h) for i in range(1, n))
    return s * h / 3


def find_root(f: Callable[[float], float], a: float, b: float) -> tuple[float, str] | None:
    """Bisection when f changes sign on [a, b], otherwise Newton from a.

    Returns (root, method) or None when no root was found.
    """
    fa, fb = f(a), f(b)
    if fa == 0:
        return a, "exact"
    if fb == 0:
        return b, "exact"
    if (fa < 0) != (fb < 0):
        lo, hi, flo = a, b, fa
        for _ in range(200):
            mid = (lo + hi) / 2
            if mid in (lo, hi):  # float precision exhausted
                break
            fm = f(mid)
            if fm == 0:
                return mid, "bisection"
            if (fm < 0) == (flo < 0):
                lo, flo = mid, fm
            else:
                hi = mid
        return (lo + hi) / 2, "bisection"
    x = a
    try:
        for _ in range(100):
            fx = f(x)
            h = 1e-6 * max(1.0, abs(x))
            d = (f(x + h) - f(x - h)) / (2 * h)
            if d == 0 or not math.isfinite(d):
                break
            nx = x - fx / d
            if abs(nx - x) <= 1e-12 * max(1.0, abs(x)):
                return (nx, "newton") if abs(f(nx)) <= 1e-8 else None
            x = nx
    except (CalcError, ArithmeticError, ValueError):
        pass
    return None


# --------------------------------------------------------------------------- #
#  The engine: safe parsing + compilation + evaluation + validation
# --------------------------------------------------------------------------- #
CMP_SPLIT = re.compile(r"(<=|>=|≠|<>|==|≤|≥|=|<|>)")
# implicit multiplication: 2x, 3pi, 2(1+1), (1+2)(3+4), (2)3
IMPLICIT = re.compile(r"(?<![A-Za-z_\d.])(\d+\.?\d*)(?![eE][+-]?\d)\s*(?=[A-Za-z_(])|\)\s*(?=[\dA-Za-z_(])")
ASSIGN = re.compile(r"^(?:let\s+([A-Za-z_]\w*)\s*(?::=|=)|([A-Za-z_]\w*)\s*:=)\s*(.+)$")
SYMBOLS = {"×": "*", "÷": "/", "−": "-", "–": "-", "√": "sqrt", "∛": "cbrt",
           "π": "pi", "τ": "tau", "φ": "phi", "θ": "theta", "²": "**2", "³": "**3",
           "^": "**", " ": " "}


@dataclass(frozen=True)
class ValueResult:
    """A plain calculation, e.g. ``2+2``."""
    value: Number
    kind = "value"


@dataclass(frozen=True)
class Assignment:
    """A variable definition, e.g. ``x := 7`` or ``let x = 7``."""
    name: str
    value: Number
    kind = "assign"


@dataclass(frozen=True)
class Check:
    """A validated (in)equality chain, e.g. ``1+1=11`` or ``1 < 2 <= 2``."""
    ok: bool
    exprs: tuple[str, ...]
    ops: tuple[str, ...]
    values: tuple[Number, ...]
    kind = "check"

    def __bool__(self):
        return self.ok


@dataclass(frozen=True)
class FunctionDef:
    """A user function definition, e.g. ``f(x) := x^2 + 1`` or ``let area(w, h) = w*h``."""
    name: str
    params: tuple[str, ...]
    body: str
    kind = "define"


Result = Union[ValueResult, Assignment, Check, FunctionDef]

FUNC_DEF = re.compile(r"^(?:let\s+(?P<a>[A-Za-z_]\w*)\s*\((?P<ap>[^()]*)\)\s*:?="
                      r"|(?P<b>[A-Za-z_]\w*)\s*\((?P<bp>[^()]*)\)\s*:=)\s*(?P<body>.+)$")


def _encode_number(v: Number):
    """JSON-safe number: ints go through hex, which has no digit limit and stays exact."""
    return {"int": format(v, "x")} if isinstance(v, int) else float(v)


def _decode_number(v) -> Number:
    if isinstance(v, dict) and isinstance(v.get("int"), str):
        return _guard_int(int(v["int"], 16))
    if isinstance(v, (int, float)) and not isinstance(v, bool) and math.isfinite(v):
        return v
    raise ValueError(f"not a number: {v!r}")


def _check_result(v) -> Number:
    if isinstance(v, bool):
        return int(v)
    if isinstance(v, complex):
        raise CalcError("Complex results are not supported")
    if isinstance(v, float):
        if not math.isfinite(v):
            raise CalcError("Undefined result")
        return v
    if isinstance(v, int):
        return v
    raise CalcError("Unsupported result")


class Expression:
    """A compiled, reusable expression. Much faster than re-parsing for repeated use.

        f = engine.compile("x^2 + 1", params=("x",))
        f(x=3)            # -> 10
        f.eval({"x": 3})  # same, without building a kwargs dict
    """
    __slots__ = ("source", "params", "_fn")

    def __init__(self, source: str, params: tuple[str, ...], fn):
        self.source, self.params, self._fn = source, params, fn

    def __call__(self, **values: Number) -> Number:
        return self.eval(values)

    def __repr__(self):
        return f"Expression({self.source!r}, params={self.params})"

    def eval(self, scope: dict | None = None) -> Number:
        try:
            v = self._fn(scope if scope is not None else {})
        except CalcError:
            raise
        except ZeroDivisionError:
            raise CalcError("Division by zero") from None
        except OverflowError:
            raise CalcError("Result too large") from None
        except statistics.StatisticsError:  # subclass of ValueError: must come first
            raise CalcError("Not enough data points") from None
        except ValueError:
            raise CalcError("Math domain error") from None
        except TypeError:
            raise CalcError("Wrong arguments for a function") from None
        except RecursionError:
            raise CalcError("Expression too deeply nested") from None
        return _check_result(v)


@dataclass(frozen=True)
class UserFunction:
    name: str
    params: tuple[str, ...]
    body: str
    expr: Expression

    @property
    def signature(self) -> str:
        return f"{self.name}({', '.join(self.params)})"


class Engine:
    """Safe calculator engine.

    Public API:
        evaluate(expr, **names) -> number
        compile(expr, params=()) -> Expression
        process(text, commit=True) -> ValueResult | Assignment | Check | FunctionDef
        set_var(name, value) / vars, ans, memory, deg
        define_function(name, params, body) / user_funcs / call_function(name, args)
        export_state() / import_state(data)  -- JSON-safe save/restore of all of the above
        angle_mode(deg)  -- context manager to temporarily switch DEG/RAD
    """

    def __init__(self, deg: bool = True):
        self.deg = deg
        self.vars: dict[str, Number] = {}
        self.user_funcs: dict[str, UserFunction] = {}
        self.ans: Number = 0
        self.memory: Number = 0
        self.funcs = self._build_funcs()
        self.reserved = set(CONSTS) | set(self.funcs) | {"ans", "m", "let", "mod"}

    # ---- function table ------------------------------------------------- #
    def _build_funcs(self):
        def trig(f, name):
            def g(x):
                if self.deg:
                    if x % 90 == 0:  # exact values at quadrant boundaries
                        q = int(x // 90) % 4
                        if name == "sin":
                            return (0.0, 1.0, 0.0, -1.0)[q]
                        if name == "cos":
                            return (1.0, 0.0, -1.0, 0.0)[q]
                        if q % 2:
                            raise CalcError("tan is undefined at odd multiples of 90°")
                        return 0.0
                    xr = math.radians(x)
                else:
                    xr = x
                    if name == "tan" and abs(math.cos(xr)) < 1e-15:
                        raise CalcError("tan is undefined at odd multiples of π/2")
                v = f(xr)
                if abs(xr) >= 1 and abs(v) < 1e-15 * abs(xr):  # e.g. sin(pi) = 1.2e-16
                    return 0.0
                return _snap(v)
            return g

        def inverse_trig(f):
            return lambda x: _snap(math.degrees(f(x))) if self.deg else f(x)

        def sqrt(x):
            if x < 0:
                raise CalcError("Square root of a negative number")
            if isinstance(x, int):
                r = math.isqrt(x)
                if r * r == x:
                    return r
            return math.sqrt(x)

        def ints(f):
            return lambda a, b: f(_as_int(a), _as_int(b))

        def logb(x, b):
            if b <= 0 or b == 1:
                raise CalcError("Log base must be positive and not 1")
            return math.log(x, b)

        def randint(a, b):
            a, b = _as_int(a), _as_int(b)
            if a > b:
                raise CalcError("randint(a, b) needs a <= b")
            return random.randint(a, b)

        return {
            "sin": trig(math.sin, "sin"), "cos": trig(math.cos, "cos"), "tan": trig(math.tan, "tan"),
            "asin": inverse_trig(math.asin), "acos": inverse_trig(math.acos), "atan": inverse_trig(math.atan),
            "sinh": math.sinh, "cosh": math.cosh, "tanh": math.tanh,
            "sqrt": sqrt, "cbrt": _cbrt, "root": _root, "abs": abs,
            "log": math.log10, "ln": math.log, "log2": math.log2, "logb": logb, "exp": math.exp,
            "floor": math.floor, "ceil": math.ceil, "round": _round,
            "sign": lambda x: (x > 0) - (x < 0), "pow": _pow,
            "fact": fact, "fib": fib, "ncr": _comb, "npr": _perm,
            "gcd": ints(math.gcd), "lcm": ints(math.lcm),
            "isprime": lambda n: int(is_prime(_checked_prime_arg(n))),
            "nextprime": lambda n: next_prime(_checked_prime_arg(n)),
            "hypot": math.hypot, "rad": math.radians, "deg": math.degrees,
            "mean": _variadic(statistics.mean, "mean"),
            "median": _variadic(statistics.median, "median"),
            "stdev": _variadic(statistics.stdev, "stdev", 2),
            "sum": _variadic(sum, "sum"), "max": _variadic(max, "max"), "min": _variadic(min, "min"),
            "rand": random.random, "randint": randint,
        }

    @property
    def functions(self) -> list[str]:
        """Names of all built-in functions."""
        return sorted(self.funcs)

    @contextmanager
    def angle_mode(self, deg: bool):
        """Temporarily evaluate trig functions in degrees (True) or radians (False)."""
        old, self.deg = self.deg, deg
        try:
            yield self
        finally:
            self.deg = old

    def _check_name(self, name: str, what="variable"):
        if not re.fullmatch(r"[A-Za-z_]\w*", name):
            raise CalcError(f"'{name}' is not a valid {what} name")
        if name in self.reserved:
            raise CalcError(f"'{name}' is a reserved name")

    def set_var(self, name: str, value: Number):
        self._check_name(name)
        self.user_funcs.pop(name, None)  # one namespace: a variable replaces a function of the same name
        self.vars[name] = value

    # ---- user-defined functions ------------------------------------------ #
    def _make_function(self, name: str, params: Iterable[str], body: str) -> UserFunction:
        params = tuple(p.strip() for p in params)
        self._check_name(name, "function")
        for p in params:
            self._check_name(p, "parameter")
        if len(set(params)) != len(params):
            raise CalcError("Parameter names must be different")
        if re.search(rf"\b{re.escape(name)}\s*\(", self.prepare(body)):
            raise CalcError("A function can't call itself")
        return UserFunction(name, params, body.strip(), self.compile(body, params))

    def define_function(self, name: str, params: Iterable[str], body: str) -> UserFunction:
        """Define (or replace) a function: define_function("f", ["x"], "x^2 + 1")."""
        uf = self._make_function(name, params, body)
        self.vars.pop(name, None)
        self.user_funcs[name] = uf
        return uf

    def call_function(self, name: str, args: list[Number]) -> Number:
        uf = self.user_funcs.get(name)
        if uf is None:
            raise CalcError(f"Unknown function '{name}'")
        if len(args) != len(uf.params):
            n = len(uf.params)
            raise CalcError(f"{name}() takes {n} argument{'' if n == 1 else 's'}")
        return uf.expr.eval(dict(zip(uf.params, args)))

    # ---- persistence ------------------------------------------------------ #
    def export_state(self) -> dict:
        """Everything the user built up (variables, functions, ANS, memory, angle mode) as JSON-safe data."""
        return {"deg": self.deg, "ans": _encode_number(self.ans), "memory": _encode_number(self.memory),
                "vars": {k: _encode_number(v) for k, v in self.vars.items()},
                "functions": [{"name": f.name, "params": list(f.params), "body": f.body}
                              for f in self.user_funcs.values()]}

    def import_state(self, data: dict) -> list[str]:
        """Restore what export_state() produced. Bad entries are skipped; returns their descriptions."""
        skipped = []
        self.deg = bool(data.get("deg", self.deg))
        for key in ("ans", "memory"):
            if key in data:
                try:
                    setattr(self, key, _decode_number(data[key]))
                except (ValueError, CalcError):
                    skipped.append(key)
        for name, v in (data.get("vars") or {}).items():
            try:
                self.set_var(name, _decode_number(v))
            except (ValueError, TypeError, CalcError):
                skipped.append(f"variable {name}")
        pending = [f for f in (data.get("functions") or []) if isinstance(f, dict)]
        for _ in range(len(pending)):  # functions may use each other: retry until nothing changes
            failed = []
            for f in pending:
                try:
                    self.define_function(f["name"], f["params"], f["body"])
                except (KeyError, TypeError, CalcError):
                    failed.append(f)
            if len(failed) == len(pending):
                break
            pending = failed
        skipped += [f"function {f.get('name')}" for f in pending if f.get("name") not in self.user_funcs]
        return skipped

    # ---- text -> python expression -------------------------------------- #
    def prepare(self, s: str) -> str:
        s = s.strip()
        s = re.sub(r"[√∛]\s*(\d+(?:\.\d+)?|[A-Za-z_]\w*)",
                   lambda m: ("sqrt(" if m.group(0)[0] == "√" else "cbrt(") + m.group(1) + ")", s)
        for k, v in SYMBOLS.items():
            s = s.replace(k, v)
        if s.count("(") != s.count(")"):
            raise CalcError("Unbalanced parentheses")
        s = re.sub(r"(\d+(?:\.\d+)?)\s*%(?!\s*[\d(A-Za-z_])", r"(\1/100)", s)
        s = re.sub(r"\bmod\b", "%", s)
        s = self._expand_factorials(s)
        s = IMPLICIT.sub(lambda m: (m.group(1) or ")") + "*", s)
        return s

    @staticmethod
    def _expand_factorials(s: str) -> str:
        while "!" in s:
            i = s.index("!")
            j = i - 1
            while j >= 0 and s[j] == " ":
                j -= 1
            if j < 0:
                raise CalcError("Nothing before '!'")
            if s[j] == ")":
                depth, k = 0, j
                while k >= 0:
                    if s[k] == ")":
                        depth += 1
                    elif s[k] == "(":
                        depth -= 1
                        if depth == 0:
                            break
                    k -= 1
                if k < 0:
                    raise CalcError("Unbalanced parentheses")
                start = k
                while start > 0 and (s[start - 1].isalnum() or s[start - 1] == "_"):
                    start -= 1
            else:
                k = j
                while k >= 0 and (s[k].isalnum() or s[k] in "._"):
                    k -= 1
                start = k + 1
                if start > j:
                    raise CalcError("Nothing before '!'")
            s = s[:start] + "fact(" + s[start:j + 1] + ")" + s[i + 1:]
        return s

    # ---- compilation: AST -> nested closures (parsed once, evaluated fast) - #
    def compile(self, expr: str, params: Iterable[str] = ()) -> Expression:
        params = tuple(params)
        py = self.prepare(expr)
        if not py:
            raise CalcError("Empty expression")
        try:
            tree = ast.parse(py, mode="eval")
            fn = self._build(tree.body, frozenset(params))
        except SyntaxError:
            raise CalcError("Syntax error - check your expression") from None
        except ValueError:  # e.g. a numeric literal longer than Python's digit limit
            raise CalcError("Invalid number or character") from None
        except (RecursionError, MemoryError):
            raise CalcError("Expression too complex") from None
        return Expression(expr, params, fn)

    def _is_value_name(self, k, params):
        return k in params or k in CONSTS or k in ("ans", "m") or k in self.vars

    def _build_name(self, k, params):
        if k in params:
            def param(s):
                try:
                    return s[k]
                except KeyError:
                    raise CalcError(f"No value given for '{k}'") from None
            return param
        if k in CONSTS:
            c = CONSTS[k]
            return lambda s: c
        if k == "ans":
            return lambda s: self.ans
        if k == "m":
            return lambda s: self.memory

        def var(s):
            try:
                return self.vars[k]
            except KeyError:
                raise CalcError(f"Unknown name '{k}'") from None
        return var

    def _build(self, n, params):
        if isinstance(n, ast.Constant):
            v = n.value
            if isinstance(v, (int, float)) and not isinstance(v, bool):
                return lambda s: v
            raise CalcError("Unsupported value")

        if isinstance(n, ast.BinOp):
            left, right, op = self._build(n.left, params), self._build(n.right, params), type(n.op)
            if op is ast.Add:
                return lambda s: left(s) + right(s)
            if op is ast.Sub:
                return lambda s: left(s) - right(s)
            if op is ast.Mult:
                return lambda s: _guard_int(left(s) * right(s))
            if op is ast.Div:
                return lambda s: _div(left(s), right(s))
            if op is ast.FloorDiv:
                return lambda s: _floordiv(left(s), right(s))
            if op is ast.Mod:
                return lambda s: _mod(left(s), right(s))
            if op is ast.Pow:
                return lambda s: _pow(left(s), right(s))
            raise CalcError("Unsupported operator")

        if isinstance(n, ast.UnaryOp):
            operand = self._build(n.operand, params)
            if isinstance(n.op, ast.USub):
                return lambda s: -operand(s)
            if isinstance(n.op, ast.UAdd):
                return operand
            raise CalcError("Unsupported operator")

        if isinstance(n, ast.Name):
            return self._build_name(n.id, params)

        if isinstance(n, ast.Call):
            if not isinstance(n.func, ast.Name) or n.keywords:
                raise CalcError("Unsupported function call")
            name = n.func.id
            args = [self._build(a, params) for a in n.args]
            f = self.funcs.get(name)
            if f is None and name in self.user_funcs:
                # looked up when called, so redefining f also updates graphs etc. that use it
                return lambda s: _guard_int(self.call_function(name, [a(s) for a in args]))
            if f is None:
                # implicit multiplication: pi(2), x(x+1), a(3)
                if len(args) == 1 and self._is_value_name(name, params):
                    base, arg = self._build_name(name, params), args[0]
                    return lambda s: _guard_int(base(s) * arg(s))
                raise CalcError(f"Unknown function '{name}'")
            if len(args) == 1:
                a0 = args[0]
                return lambda s: _guard_int(f(a0(s)))
            return lambda s: _guard_int(f(*[a(s) for a in args]))

        raise CalcError("Unsupported syntax")

    # ---- evaluation ------------------------------------------------------ #
    def evaluate(self, expr: str, **names: Number) -> Number:
        """Evaluate ``expr``; keyword arguments provide extra names, e.g. evaluate("x^2", x=3)."""
        return self.compile(expr, names).eval(names)

    # ---- top level: value / assignment / validation ----------------------- #
    def process(self, raw: str, commit: bool = True) -> Result:
        """Interpret a line of user input. With ``commit=False`` nothing is stored (preview)."""
        raw = raw.strip()
        if not raw:
            raise CalcError("Empty expression")

        m = FUNC_DEF.match(raw)
        if m:
            name, params = m.group("a") or m.group("b"), m.group("ap") if m.group("a") else m.group("bp")
            params = [p for p in params.split(",")] if params.strip() else []
            make = self.define_function if commit else self._make_function
            uf = make(name, params, m.group("body"))
            return FunctionDef(uf.name, uf.params, uf.body)

        m = ASSIGN.match(raw)
        if m:
            name, rhs = m.group(1) or m.group(2), m.group(3)
            self._check_name(name)
            val = self.evaluate(rhs)
            if commit:
                self.set_var(name, val)
            return Assignment(name, val)

        parts = CMP_SPLIT.split(raw)
        if len(parts) > 1:
            exprs, ops = parts[0::2], parts[1::2]
            if len(ops) == 1 and not exprs[1].strip() and exprs[0].strip():  # "5+3=" -> just compute
                return self._value(exprs[0], commit)
            if any(not e.strip() for e in exprs):
                raise CalcError("Missing value next to a comparison sign")
            vals = [self.evaluate(e) for e in exprs]
            ok = all(self._cmp(vals[i], op, vals[i + 1]) for i, op in enumerate(ops))
            return Check(ok, tuple(exprs), tuple(ops), tuple(vals))

        return self._value(raw, commit)

    def _value(self, expr, commit):
        v = self.evaluate(expr)
        if commit:
            self.ans = v
        return ValueResult(v)

    @staticmethod
    def _cmp(a, op, b) -> bool:
        if op in ("=", "=="):
            return close(a, b)
        if op in ("≠", "<>"):
            return not close(a, b)
        if op == "<":
            return a < b and not close(a, b)
        if op == ">":
            return a > b and not close(a, b)
        if op in ("<=", "≤"):
            return a < b or close(a, b)
        return a > b or close(a, b)


def calc(expr: str, *, deg: bool = True, **names: Number) -> Number:
    """One-shot convenience: calc("2^10") -> 1024, calc("x^2", x=4) -> 16."""
    return Engine(deg=deg).evaluate(expr, **names)


# --------------------------------------------------------------------------- #
#  Graph helpers
# --------------------------------------------------------------------------- #
# --------------------------------------------------------------------------- #
#  Vectorised evaluation and 3D meshes (NumPy)
# --------------------------------------------------------------------------- #
def _vector_funcs(np):
    from functools import reduce

    def fold(op):
        return lambda *args: reduce(op, args)
    return {
        "sin": np.sin, "cos": np.cos, "tan": np.tan, "asin": np.arcsin, "acos": np.arccos, "atan": np.arctan,
        "sinh": np.sinh, "cosh": np.cosh, "tanh": np.tanh, "sqrt": np.sqrt, "cbrt": np.cbrt, "abs": np.abs,
        "log": np.log10, "ln": np.log, "log2": np.log2, "exp": np.exp, "floor": np.floor, "ceil": np.ceil,
        "sign": np.sign, "hypot": np.hypot, "rad": np.radians, "deg": np.degrees, "pow": np.power,
        "logb": lambda x, b: np.log(x) / np.log(b),
        "root": lambda x, n: np.where((x < 0) & (np.mod(n, 2) == 0), np.nan, np.sign(x) * np.abs(x) ** (1.0 / n)),
        # element-wise min/max: union and intersection when building shapes from implicit surfaces
        "min": fold(np.minimum), "max": fold(np.maximum), "sum": fold(np.add),
        "mean": lambda *args: reduce(np.add, args) / len(args),
    }


def compile_vector(engine, expr, params):
    """Compile ``expr`` to work on whole NumPy arrays at once (graphs need 10^4-10^6 points).

    The expression first goes through the normal compiler, so syntax and error messages are the
    calculator's own. Trig is in radians; undefined points come out as NaN. Functions without a
    NumPy version (fact, ncr, ...) fall back to the scalar engine point by point, which is slow but
    still correct."""
    import numpy as np
    engine.compile(expr, params)  # validation only
    fn = _vector_build(engine, ast.parse(engine.prepare(expr), mode="eval").body, frozenset(params), np,
                       _vector_funcs(np))

    def run(scope):
        with np.errstate(all="ignore"):
            out = np.asarray(fn(scope), dtype=float)
        return np.where(np.isfinite(out), out, np.nan)  # like the calculator: 1/0 and log(0) are undefined, not ±inf
    return run


def _vector_build(engine, n, params, np, vfuncs):
    build = lambda node: _vector_build(engine, node, params, np, vfuncs)
    if isinstance(n, ast.Constant):
        value = float(n.value)
        return lambda s: value
    if isinstance(n, ast.BinOp):
        left, right = build(n.left), build(n.right)
        op = {ast.Add: np.add, ast.Sub: np.subtract, ast.Mult: np.multiply, ast.Div: np.true_divide,
              ast.FloorDiv: np.floor_divide, ast.Mod: np.mod, ast.Pow: np.power}[type(n.op)]
        return lambda s: op(left(s), right(s))
    if isinstance(n, ast.UnaryOp):
        operand = build(n.operand)
        return (lambda s: np.negative(operand(s))) if isinstance(n.op, ast.USub) else operand
    if isinstance(n, ast.Name):
        k = n.id
        if k in params:
            return lambda s: s[k]
        if k in CONSTS:
            value = CONSTS[k]
            return lambda s: value
        if k in ("ans", "m"):
            return lambda s: _as_float(engine.ans if k == "ans" else engine.memory)

        def var(s):
            if k not in engine.vars:
                raise CalcError(f"Unknown name '{k}'")
            return _as_float(engine.vars[k])
        return var
    # a call (validated already): built-in, user function, implicit multiplication, or scalar fallback
    name, args = n.func.id, [build(a) for a in n.args]
    if name in vfuncs:
        f = vfuncs[name]
        return lambda s: f(*[a(s) for a in args])
    if name in engine.user_funcs:
        uf = engine.user_funcs[name]
        body = compile_vector(engine, uf.body, uf.params)
        return lambda s: body(dict(zip(uf.params, [a(s) for a in args])))
    if name not in engine.funcs:  # pi(2), a(x+1): multiplication
        base = build(ast.Name(id=name))
        return lambda s: np.multiply(base(s), args[0](s))
    scalar = engine.funcs[name]

    def safe(*values):
        try:
            return float(scalar(*values))
        except Exception:
            return math.nan
    vectorised = np.vectorize(safe, otypes=[float])
    return lambda s: vectorised(*[a(s) for a in args])


def _as_float(v):
    try:
        return float(v)
    except OverflowError:
        return math.inf


def _clean_mesh(np, vertices, faces):
    """Drop triangles touching undefined points, then drop vertices no triangle uses."""
    ok = np.isfinite(vertices).all(axis=1)
    faces = faces[ok[faces].all(axis=1)]
    if not len(faces):
        raise CalcError("The shape is undefined everywhere in this range")
    used, remap = np.unique(faces, return_inverse=True)
    return vertices[used], remap.reshape(faces.shape).astype(np.uint32)


def _grid_faces(np, rows, cols):
    i, j = np.meshgrid(np.arange(rows - 1), np.arange(cols - 1), indexing="ij")
    a = (i * cols + j).ravel()
    b, c = a + cols, a + 1
    return np.concatenate([np.stack([a, b, b + 1], 1), np.stack([a, b + 1, c], 1)])


@dataclass
class MeshPart:
    """One surface of a 3D plot. ``rgba`` None means 'colour by height' (a single plain surface);
    ``vertex_colors`` (per-vertex RGBA) is used instead when parts are joined into one solid."""
    vertices: object
    faces: object
    rgba: tuple | None = None
    alpha: float = 1.0
    vertex_colors: object = None


def styled_parts(src):
    """'expr @style; expr @style; …' -> [(expr, style)]. A style is a colour and/or an opacity: '@pink 40%'."""
    parts = []
    for chunk in src.split(";"):
        expr, _, style = chunk.partition("@")
        if expr.strip():
            parts.append((expr.strip(), style.strip()))
        elif style.strip():
            raise CalcError("A colour needs a shape before it, like  x^2 + y^2 + z^2 = 1 @pink")
    if not parts:
        raise CalcError("Type something to plot")
    return parts


def parse_style(style, index, count):
    """'pink 40%' -> ((r, g, b, a) or None, a). No colour: height colouring for a lone surface,
    otherwise the next colour of the graph palette, so several surfaces are told apart."""
    color, alpha = None, 1.0
    for token in style.split():
        if token.endswith("%"):
            try:
                alpha = min(1.0, max(0.05, float(token[:-1]) / 100))
            except ValueError:
                raise CalcError(f"'{token}' isn't an opacity: use something like 40%") from None
        elif color is None:
            color = token
        else:
            raise CalcError(f"Two colours for one surface: '{color}' and '{token}'")
    if color is None:
        if count == 1:
            return None, alpha
        color = GRAPH_COLORS[index % len(GRAPH_COLORS)]
    from matplotlib.colors import to_rgba
    try:
        r, g, b, _ = to_rgba(color)
    except ValueError:
        raise CalcError(f"Unknown colour '{color}': use a name like pink or tan, or #ff69b4") from None
    return (r, g, b, alpha), alpha


def heightmap_mesh(engine, src, x0, x1, y0, y1, n=150):
    """z = f(x, y) as a triangle mesh; spikes near asymptotes are cut out. Returns (vertices, faces, (lo, hi))."""
    import numpy as np
    X, Y = np.meshgrid(np.linspace(x0, x1, n), np.linspace(y0, y1, n), indexing="ij")
    Z = np.broadcast_to(compile_vector(engine, src, ("x", "y"))({"x": X, "y": Y}), X.shape).copy()
    finite = Z[np.isfinite(Z)]
    if not finite.size:
        raise CalcError("z(x, y) is undefined everywhere in this range")
    lo, hi = (float(v) for v in np.percentile(finite, [1, 99]))
    if hi - lo < 1e-9:
        lo, hi = lo - 1, hi + 1
    span = hi - lo
    Z[(Z < lo - span) | (Z > hi + span)] = np.nan  # cut off spikes near asymptotes
    vertices = np.stack([X.ravel(), Y.ravel(), np.clip(Z, lo - span * 0.1, hi + span * 0.1).ravel()], 1)
    return (*_clean_mesh(np, vertices, _grid_faces(np, n, n)), (lo, hi))


def heightmap_parts(engine, src, x0, x1, y0, y1, n=150):
    """One or more height maps  'z1 @style; z2 @style'  -> ([MeshPart], combined (lo, hi) for colouring)."""
    parts, lows, highs = [], [], []
    styled = styled_parts(src)
    for i, (expr, style) in enumerate(styled):
        rgba, alpha = parse_style(style, i, len(styled))
        vertices, faces, (lo, hi) = heightmap_mesh(engine, re.sub(r"^\s*z\s*=\s*", "", expr), x0, x1, y0, y1, n)
        parts.append(MeshPart(vertices, faces, rgba, alpha))
        lows.append(lo)
        highs.append(hi)
    return parts, (min(lows), max(highs))


def surface_mesh(engine, src, u0, u1, v0, v1, n=160):
    """Parametric surface  x(u,v), y(u,v), z(u,v)  as a triangle mesh: spheres, tori, shells, Klein bottles..."""
    import numpy as np
    parts = split_numbers(src)
    if len(parts) != 3:
        raise CalcError("Write the surface as   x(u,v), y(u,v), z(u,v)")
    U, V = np.meshgrid(np.linspace(u0, u1, n), np.linspace(v0, v1, n), indexing="ij")
    scope = {"u": U, "v": V}
    xyz = [np.broadcast_to(compile_vector(engine, p, ("u", "v"))(scope), U.shape).ravel() for p in parts]
    return _clean_mesh(np, np.stack(xyz, 1), _grid_faces(np, n, n))


def surface_parts(engine, src, u0, u1, v0, v1, n=160):
    """One or more (u, v) surfaces  'x, y, z @style; x, y, z @style'  -> [MeshPart]."""
    styled = styled_parts(src)
    return [MeshPart(*surface_mesh(engine, expr, u0, u1, v0, v1, n), *parse_style(style, i, len(styled)))
            for i, (expr, style) in enumerate(styled)]


def implicit_function(src):
    """'lhs = rhs' -> 'lhs - (rhs)'; a lone expression is taken as  F = 0."""
    sides = src.split("=")
    if len(sides) > 2 or any(not s.strip() for s in sides):
        raise CalcError("Write the surface as  F(x, y, z) = 0  or  left side = right side")
    return sides[0] if len(sides) == 1 else f"({sides[0]}) - ({sides[1]})"


def _marching_cubes(np, field, lo, hi, n):
    from vispy.geometry.isosurface import isosurface
    with np.errstate(all="ignore"):  # VisPy's index arithmetic warns harmlessly on NumPy 2
        vertices, faces = isosurface(field, 0.0)
    return lo + vertices * (hi - lo) / (n - 1), faces.astype(np.uint32)


def implicit_parts(engine, src, lo, hi, n=72, join=False):
    """Implicit surfaces  'F1 = 0 @style; F2 = 0 @style'  inside the cube [lo, hi]^3 (marching cubes).

    By default every part is its own surface, so surfaces pass through each other and their
    intersections stay visible. With ``join`` the parts become one solid (the minimum of their F),
    each point coloured by the part it lies on: modelling, e.g. icing on a donut."""
    import numpy as np
    styled = styled_parts(src)
    styles = [parse_style(style, i, len(styled)) for i, (_, style) in enumerate(styled)]  # check before heavy work
    fns = [compile_vector(engine, implicit_function(expr), ("x", "y", "z")) for expr, _ in styled]
    g = np.linspace(lo, hi, n)
    X, Y, Z = np.meshgrid(g, g, g, indexing="ij")
    fields = []
    for fn in fns:
        values = np.broadcast_to(fn({"x": X, "y": Y, "z": Z}), X.shape)
        fields.append(np.where(np.isfinite(values), values, 1e9))  # undefined points count as outside
    crosses = lambda field: (field < 0).any() and (field > 0).any()
    if join and len(styled) > 1:
        F = np.minimum.reduce(fields)
        if not crosses(F):
            raise CalcError("The surface doesn't pass through this box: try a bigger range")
        vertices, faces = _marching_cubes(np, F, lo, hi, n)
        at = {"x": vertices[:, 0], "y": vertices[:, 1], "z": vertices[:, 2]}
        owner = np.stack([np.nan_to_num(np.broadcast_to(fn(at), (len(vertices),)), nan=np.inf) for fn in fns],
                         1).argmin(1)
        return [MeshPart(vertices, faces, vertex_colors=np.array([rgba for rgba, _ in styles], np.float32)[owner])]
    parts = [MeshPart(*_marching_cubes(np, field, lo, hi, n), *style)
             for field, style in zip(fields, styles) if crosses(field)]
    if not parts:
        raise CalcError("The surface doesn't pass through this box: try a bigger range")
    return parts


def _restore_depth_writes(canvas):
    """See-through surfaces are drawn with depth writes off and are drawn last, so OpenGL would start
    the next frame with depth writes still off. glClear then can't clear the depth buffer, and every
    3D object fails the depth test against stale values: the whole 3D view randomly blanks. Turn depth
    writes back on before each frame's clear."""
    canvas.events.draw.connect(lambda event: canvas.context.set_depth_mask(True), position="first")


def merge_parts(parts):
    """All parts as one (vertices, faces) mesh, e.g. for STL export."""
    import numpy as np
    offsets = np.cumsum([0] + [len(p.vertices) for p in parts[:-1]])
    return (np.concatenate([p.vertices for p in parts]),
            np.concatenate([p.faces + off for p, off in zip(parts, offsets)]).astype(np.uint32))


def write_stl(path, vertices, faces):
    """Binary STL: the standard 3D-printing / 3D-modelling exchange format."""
    import numpy as np
    tri = vertices[faces].astype(np.float32)
    normals = np.cross(tri[:, 1] - tri[:, 0], tri[:, 2] - tri[:, 0])
    length = np.linalg.norm(normals, axis=1, keepdims=True)
    normals = np.divide(normals, length, out=np.zeros_like(normals), where=length > 0)
    records = np.zeros(len(faces), dtype=[("normal", "<f4", (3,)), ("vertices", "<f4", (3, 3)), ("attr", "<u2")])
    records["normal"], records["vertices"] = normals, tri
    with open(path, "wb") as f:
        f.write(b"UltraCalc mesh".ljust(80, b" "))
        f.write(np.uint32(len(faces)).tobytes())
        f.write(records.tobytes())


def _preload_matplotlib():
    try:  # only the GUI-free parts; the Tk backend is imported on the main thread when needed
        import matplotlib.backends.backend_agg  # noqa: F401
        import matplotlib.figure  # noqa: F401
    except ImportError:
        pass
    try:  # the GPU 3D view's library (its Tk/OpenGL backend loads only when the 3D view is created)
        if sys.platform.startswith("linux"):
            os.environ.setdefault("PYOPENGL_PLATFORM", "glx")
        import vispy.scene  # noqa: F401
    except Exception:
        pass


GRAPH_COLORS = ["#4EA1FF", "#FF6B6B", "#2FD38E", "#FFB020", "#B36BFF"]
MAX_GRAPHS = len(GRAPH_COLORS)
RANGE_KEYS = ("xmin", "xmax", "ymin", "ymax")
TWO_PI = ("0", "2pi")

# Graph tab modes: input label, which range fields are shown (relabelled), defaults, presets
# (expression, ranges-or-None), the Matplotlib projection and the method that draws it.
GRAPH_MODES = {
    "y = f(x)": dict(
        label="f(x) =", fields=("xmin", "xmax", "ymin", "ymax"), defaults=("-10", "10", "", ""),
        expr="sin(x); x^2/10; 0.5*x", projection=None, draw="_draw_function",
        info="Separate functions with ';' (trig in radians). Hover to trace · scroll to zoom · drag to pan · "
             "double-click to reset",
        presets={"Waves": ("sin(x); cos(x)", None), "Parabolas": ("x^2; -x^2+4; 0.2*x^2-3", None),
                 "Rational": ("1/x; 1/(x^2+1)", None), "Growth": ("exp(x/3); ln(x); sqrt(x)", None),
                 "Bell curve": ("exp(-x^2/2)/sqrt(2*pi)", None), "Cubic": ("x^3 - 3*x", None)}),
    "Polar": dict(
        label="r(θ) =", fields=("θ from", "θ to"), defaults=(*TWO_PI, "", ""),
        expr="cos(4θ); 1 + cos(θ)", projection="polar", draw="_draw_polar",
        info="Separate curves with ';'. Write the angle as θ, theta or t (radians).",
        presets={"Rose": ("cos(4θ)", TWO_PI), "Cardioid": ("1 + cos(θ)", TWO_PI),
                 "Limaçon": ("1 + 2cos(θ)", TWO_PI), "Spiral": ("θ/(2pi)", ("0", "8pi")),
                 "Butterfly": ("exp(sin(θ)) - 2cos(4θ) + sin((2θ - pi)/24)^5", ("0", "24pi"))}),
    "Parametric": dict(
        label="x(t), y(t) =", fields=("t from", "t to"), defaults=(*TWO_PI, "", ""),
        expr="sin(3t), sin(2t)", projection=None, draw="_draw_parametric",
        info="Write each curve as  x(t), y(t)  and separate curves with ';'.",
        presets={"Lissajous": ("sin(3t), sin(2t)", TWO_PI), "Circle & ellipse": ("cos(t), sin(t); 2cos(t), sin(t)", TWO_PI),
                 "Heart": ("16sin(t)^3, 13cos(t) - 5cos(2t) - 2cos(3t) - cos(4t)", TWO_PI),
                 "Spirograph": ("cos(t) + cos(6t)/2 + sin(14t)/3, sin(t) + sin(6t)/2 + cos(14t)/3", TWO_PI)}),
    "3D": dict(
        label="z(x, y) =", fields=("xmin", "xmax", "ymin", "ymax"), defaults=("-8", "8", "-8", "8"),
        expr="sin(sqrt(x^2 + y^2))", projection="3d", draw="_draw_3d_mpl", mesh="_mesh_heightmap",
        info="z(x, y); several surfaces with ';', styled like  @orange 50%. Drag to rotate, right-drag to zoom. "
             "Save… exports STL.",
        presets={"Ripple": ("sin(sqrt(x^2 + y^2))", ("-10", "10", "-10", "10")),
                 "Tangent plane": ("x^2 - y^2 @royalblue; 0.75 + 2(x - 1) - (y - 0.5) @orange 55%", ("-2", "2", "-2", "2")),
                 "Saddle": ("x^2 - y^2", ("-3", "3", "-3", "3")), "Egg crate": ("sin(x)*cos(y)", ("-6", "6", "-6", "6")),
                 "Gaussian hill": ("4exp(-(x^2 + y^2)/6)", ("-6", "6", "-6", "6")),
                 "Monkey saddle": ("x^3 - 3x*y^2", ("-2", "2", "-2", "2"))}),
    "Surface": dict(
        label="x, y, z (u, v) =", fields=("u from", "u to", "v from", "v to"), defaults=(*TWO_PI, *TWO_PI),
        expr="(2 + cos(v))cos(u), (2 + cos(v))sin(u), sin(v)", projection="3d", draw="_draw_3d_mpl",
        mesh="_mesh_param_surface",
        info="x(u,v), y(u,v), z(u,v); several surfaces with ';', styled like  @gold 40%. Drag to rotate. "
             "Save… exports STL.",
        presets={"Torus": ("(2 + cos(v))cos(u), (2 + cos(v))sin(u), sin(v)", (*TWO_PI, *TWO_PI)),
                 "Sphere in torus": ("(2 + cos(v))cos(u), (2 + cos(v))sin(u), sin(v) @deepskyblue 35%; "
                                     "1.4cos(u)sin(v/2), 1.4sin(u)sin(v/2), 1.4cos(v/2) @tomato", (*TWO_PI, *TWO_PI)),
                 "Sphere": ("cos(u)sin(v), sin(u)sin(v), cos(v)", (*TWO_PI, "0", "pi")),
                 "Seashell": ("2(1 - exp(u/(6pi)))cos(u)cos(v/2)^2, 2(exp(u/(6pi)) - 1)sin(u)cos(v/2)^2, "
                              "1 - exp(u/(3pi)) - sin(v) + exp(u/(6pi))sin(v)", ("0", "6pi", *TWO_PI)),
                 "Klein bottle": ("(2 + cos(u/2)sin(v) - sin(u/2)sin(2v))cos(u), "
                                  "(2 + cos(u/2)sin(v) - sin(u/2)sin(2v))sin(u), sin(u/2)sin(v) + cos(u/2)sin(2v)",
                                  (*TWO_PI, *TWO_PI)),
                 "Möbius strip": ("(1 + v/2 cos(u/2))cos(u), (1 + v/2 cos(u/2))sin(u), v/2 sin(u/2)",
                                  (*TWO_PI, "-1", "1")),
                 "Spiral horn": ("(1 + 0.2v)cos(v)(1 + 0.3cos(u)), (1 + 0.2v)sin(v)(1 + 0.3cos(u)), 0.4v + 0.3sin(u)",
                                 ("0", "2pi", "0", "6pi"))}),
    "Implicit": dict(
        label="F(x, y, z) =", fields=("box from", "box to", "detail"), defaults=("-2", "2", "72", ""),
        expr="x^2 + y^2 + z^2 = 1", projection="3d", draw="_draw_3d_mpl", mesh="_mesh_implicit",
        info="F(x, y, z) = 0; several surfaces with ';', styled like  @pink 40%. min/max join and carve shapes; "
             "'join parts' merges surfaces into one solid. Save… exports STL.",
        presets={"Iced donut": ("sqrt((sqrt(x^2 + y^2) - 1)^2 + z^2) - 0.45 @burlywood; "
                                "max(sqrt((sqrt(x^2 + y^2) - 1)^2 + z^2) - 0.52, 0.05 - z + 0.12sin(6x)cos(6y)) @hotpink",
                                ("-1.7", "1.7", "110")),
                 "Sphere": ("x^2 + y^2 + z^2 = 1", ("-1.5", "1.5", "72")),
                 "Sphere cut by plane": ("x^2 + y^2 + z^2 = 1 @royalblue 45%; z = 0.4x + 0.25 @orange", ("-1.4", "1.4", "96")),
                 "Level sets": ("x^2 + y^2 + z^2 = 0.5 @tomato; x^2 + y^2 + z^2 = 1.2 @gold 45%; "
                                "x^2 + y^2 + z^2 = 2.2 @deepskyblue 20%", ("-1.6", "1.6", "80")),
                 "Torus": ("(sqrt(x^2 + y^2) - 1.2)^2 + z^2 = 0.2", ("-2", "2", "80")),
                 "Heart": ("(x^2 + 9/4y^2 + z^2 - 1)^3 - x^2 z^3 - 9/80y^2 z^3 = 0", ("-1.5", "1.5", "96")),
                 "Gyroid": ("sin(x)cos(y) + sin(y)cos(z) + sin(z)cos(x) = 0", ("-5", "5", "96")),
                 "Metaballs": ("1/((x - 0.8)^2 + y^2 + z^2) + 1/((x + 0.8)^2 + y^2 + z^2) + 1/(x^2 + (y - 0.9)^2 + z^2) = 3",
                               ("-2.2", "2.2", "80")),
                 # cube ∩ sphere, minus three cylinders: the classic constructive-solid-geometry example
                 "Carved cube": ("max(max(abs(x), abs(y), abs(z)) - 1, sqrt(x^2 + y^2 + z^2) - 1.35, "
                                 "0.55 - min(sqrt(y^2 + z^2), sqrt(x^2 + z^2), sqrt(x^2 + y^2))) = 0",
                                 ("-1.6", "1.6", "96"))}),
}


def split_numbers(text: str) -> list[str]:
    """Split '1, 2, sqrt(9)' or '1 2 3' into tokens, keeping function arguments intact."""
    parts, depth, cur = [], 0, []
    for ch in text:
        depth += (ch == "(") - (ch == ")")
        if ch in ",;\n" and depth == 0:
            parts.append("".join(cur))
            cur = []
        else:
            cur.append(ch)
    parts.append("".join(cur))
    if len(parts) == 1:  # no separators: fall back to whitespace
        parts = text.split()
    return [p.strip() for p in parts if p.strip()]


# --------------------------------------------------------------------------- #
#  Ripple button (Material-style "ink" that expands from the click point)
# --------------------------------------------------------------------------- #
def _rgb(widget, color):
    return tuple(v >> 8 for v in widget.winfo_rgb(color))


def _blend(a, b, t):
    return "#%02x%02x%02x" % tuple(round(x + (y - x) * t) for x, y in zip(a, b))


# --------------------------------------------------------------------------- #
#  Animation: easing curves from Chromium's ui/gfx/animation/tween.cc
# --------------------------------------------------------------------------- #
def ease_out(t):   # Tween::EASE_OUT
    return 1 - (1 - t) ** 2


def ease_in(t):    # Tween::EASE_IN
    return t * t


def _cubic_bezier(x1, y1, x2, y2):
    def bez(s, a, b):
        return 3 * a * s * (1 - s) ** 2 + 3 * b * s * s * (1 - s) + s ** 3

    def curve(t):
        lo, hi = 0.0, 1.0
        for _ in range(24):  # solve x(s) = t by bisection; x is monotonic for these curves
            mid = (lo + hi) / 2
            if bez(mid, x1, x2) < t:
                lo = mid
            else:
                hi = mid
        return bez((lo + hi) / 2, y1, y2)
    return curve


def ease_in_out(t):  # Tween::EASE_IN_OUT
    return (t * 2) ** 2 / 2 if t < 0.5 else 1 - ((t - 1) * 2) ** 2 / 2


fast_out_slow_in = _cubic_bezier(0.4, 0, 0.2, 1)  # Tween::FAST_OUT_SLOW_IN, Chrome's movement curve
HOVER_MS = 200                                    # GlowHoverController's default duration
THEME_FADE_MS = 450


# --------------------------------------------------------------------------- #
#  Whole-window crossfade (used for the light/dark switch)
# --------------------------------------------------------------------------- #
class _XImage(ctypes.Structure):
    _fields_ = [("width", ctypes.c_int), ("height", ctypes.c_int), ("xoffset", ctypes.c_int),
                ("format", ctypes.c_int), ("data", ctypes.c_void_p), ("byte_order", ctypes.c_int),
                ("bitmap_unit", ctypes.c_int), ("bitmap_bit_order", ctypes.c_int), ("bitmap_pad", ctypes.c_int),
                ("depth", ctypes.c_int), ("bytes_per_line", ctypes.c_int), ("bits_per_pixel", ctypes.c_int),
                ("red_mask", ctypes.c_ulong), ("green_mask", ctypes.c_ulong), ("blue_mask", ctypes.c_ulong)]


_X_ERROR_HANDLER = ctypes.CFUNCTYPE(ctypes.c_int, ctypes.c_void_p, ctypes.c_void_p)


def capture_window(widget):
    """Pixel-exact snapshot of a mapped Tk window as a PhotoImage, or None where unsupported.

    X11 only (also XWayland), via XGetImage from libX11 through ctypes: no extra dependencies.
    Only the common 32-bit little-endian TrueColor layout is handled; anything else returns None.
    """
    if widget.tk.call("tk", "windowingsystem") != "x11" or not widget.winfo_viewable():
        return None
    try:
        x11 = ctypes.CDLL(ctypes.util.find_library("X11") or "libX11.so.6")
    except OSError:
        return None
    x11.XOpenDisplay.restype = ctypes.c_void_p
    x11.XOpenDisplay.argtypes = [ctypes.c_char_p]
    x11.XGetImage.restype = ctypes.POINTER(_XImage)
    x11.XGetImage.argtypes = [ctypes.c_void_p, ctypes.c_ulong, ctypes.c_int, ctypes.c_int,
                              ctypes.c_uint, ctypes.c_uint, ctypes.c_ulong, ctypes.c_int]
    x11.XSetErrorHandler.restype = ctypes.c_void_p
    x11.XSetErrorHandler.argtypes = [ctypes.c_void_p]
    for name in ("XFree", "XCloseDisplay"):
        getattr(x11, name).argtypes = [ctypes.c_void_p]
    display = x11.XOpenDisplay(None)
    if not display:
        return None
    # Xlib's default error handler exits the process; ignore errors for this call, then restore Tk's
    ignore = _X_ERROR_HANDLER(lambda d, e: 0)
    previous = x11.XSetErrorHandler(ctypes.cast(ignore, ctypes.c_void_p))
    try:
        w, h = widget.winfo_width(), widget.winfo_height()
        img = x11.XGetImage(display, widget.winfo_id(), 0, 0, w, h, (1 << 64) - 1 if ctypes.sizeof(ctypes.c_ulong) == 8 else 0xFFFFFFFF, 2)  # ZPixmap
        if not img:
            return None
        try:
            im = img.contents
            if (im.bits_per_pixel != 32 or im.byte_order != 0 or im.width != w or im.height != h
                    or (im.red_mask, im.green_mask, im.blue_mask) != (0xFF0000, 0xFF00, 0xFF)):
                return None
            raw = ctypes.string_at(im.data, im.bytes_per_line * h)
        finally:
            if img.contents.data:
                x11.XFree(img.contents.data)
            x11.XFree(img)
    finally:
        x11.XSetErrorHandler(previous)
        x11.XCloseDisplay(display)
    if len(raw) != w * 4 * h:  # padded rows: keep only the pixels
        stride = len(raw) // h
        raw = b"".join(raw[y * stride:y * stride + w * 4] for y in range(h))
    rgb = bytearray(w * h * 3)
    rgb[0::3], rgb[1::3], rgb[2::3] = raw[2::4], raw[1::4], raw[0::4]  # BGRX -> RGB, at C speed
    return tk.PhotoImage(master=widget, data=b"P6 %d %d 255\n" % (w, h) + bytes(rgb), format="ppm")


_KWIN_BLEND = None  # cached: is KDE's "blendchanges" compositor effect available?


def _dbus_send(*args):
    try:
        return subprocess.run(["dbus-send", "--session", "--print-reply", "--dest=org.kde.KWin", *args],
                              capture_output=True, text=True, timeout=1.5)
    except (OSError, subprocess.SubprocessError):
        return None


def kwin_blend_available():
    global _KWIN_BLEND
    if _KWIN_BLEND is None:
        _KWIN_BLEND = False
        if "KDE" in os.environ.get("XDG_CURRENT_DESKTOP", "") and shutil.which("dbus-send"):
            r = _dbus_send("/Effects", "org.kde.kwin.Effects.isEffectLoaded", "string:blendchanges")
            _KWIN_BLEND = bool(r and r.returncode == 0 and "boolean true" in r.stdout)
    return _KWIN_BLEND


def kwin_blend(delay_ms):
    """Ask KWin to hold the current screen image for ``delay_ms`` and then crossfade (400 ms,
    InOutCubic) to whatever is on screen by then. This is the effect Plasma itself uses when the
    colour scheme changes; it needs no extra windows, so no compositor popup animations interfere."""
    r = _dbus_send("/org/kde/KWin/BlendChanges", "org.kde.KWin.BlendChanges.start", f"int32:{int(delay_ms)}")
    return bool(r and r.returncode == 0)


def _portal_save_file(parent, title, current_name, folder, filters):
    """Blocking call to xdg-desktop-portal's FileChooser.SaveFile, which shows the desktop's own
    Save dialog (KDE's on Plasma, GNOME's on GNOME). Returns the chosen path, or None if cancelled.
    Raises if the portal (or the jeepney D-Bus library) isn't available."""
    from urllib.parse import unquote, urlparse

    from jeepney import DBusAddress, MatchRule, message_bus, new_method_call
    from jeepney.io.blocking import Proxy, open_dbus_connection
    conn = open_dbus_connection(bus="SESSION")
    try:
        token = f"ultracalc{os.getpid()}_{time.monotonic_ns()}"
        sender = conn.unique_name[1:].replace(".", "_")
        rule = MatchRule(type="signal", interface="org.freedesktop.portal.Request", member="Response",
                         path=f"/org/freedesktop/portal/desktop/request/{sender}/{token}")
        Proxy(message_bus, conn).AddMatch(rule)
        portal = DBusAddress("/org/freedesktop/portal/desktop", bus_name="org.freedesktop.portal.Desktop",
                             interface="org.freedesktop.portal.FileChooser")
        filter_list = [(label, [(0, f"*.{ext}")]) for label, ext in filters]
        options = {"handle_token": ("s", token), "current_name": ("s", current_name),
                   "current_folder": ("ay", os.fsencode(folder) + b"\0"),
                   "filters": ("a(sa(us))", filter_list), "current_filter": ("(sa(us))", filter_list[0])}
        with conn.filter(rule) as responses:
            conn.send_and_get_reply(new_method_call(portal, "SaveFile", "ssa{sv}", (parent, title, options)))
            code, results = conn.recv_until_filtered(responses).body  # waits until the dialog is closed
        uris = results.get("uris", ("as", []))[1]
        if code != 0 or not uris:
            return None
        path = unquote(urlparse(uris[0]).path)
        if not any(path.lower().endswith("." + ext) for _, ext in filters):  # typed a name without extension
            chosen = results.get("current_filter", (None, filter_list[0]))[1]
            path += "." + chosen[1][0][1].lstrip("*.")
        return path
    finally:
        conn.close()


def ask_save_path(root, title, current_name, filters, callback, folder=None):
    """Show the desktop's native Save dialog without freezing the app, then call ``callback(path or None)``
    on the Tk thread. ``filters`` is [(label, extension), ...]. Falls back to Tk's own dialog.

    The portal call blocks until the user answers, so it runs on a worker thread; blocking the Tk
    thread instead would freeze the window (and KWin greys out windows that stop responding)."""
    folder = folder if folder and os.path.isdir(folder) else os.path.expanduser("~")
    parent = f"x11:{int(root.wm_frame(), 16):x}" if root.tk.call("tk", "windowingsystem") == "x11" else ""
    answer = queue.Queue()

    def worker():
        try:
            answer.put(("ok", _portal_save_file(parent, title, current_name, folder, filters)))
        except Exception:
            answer.put(("unavailable", None))
    threading.Thread(target=worker, daemon=True).start()

    def poll():
        try:
            status, path = answer.get_nowait()
        except queue.Empty:
            root.after(100, poll)
            return
        if status == "unavailable":
            path = filedialog.asksaveasfilename(parent=root, title=title, initialfile=current_name, initialdir=folder,
                                                defaultextension="." + filters[0][1],
                                                filetypes=[(label, f"*.{ext}") for label, ext in filters]) or None
        callback(path)
    root.after(100, poll)


def crossfade_window(root, change, ms=THEME_FADE_MS):
    """Apply ``change()`` (e.g. a theme switch) as a gradual crossfade instead of a one-frame swap.

    Tk widgets can't be translucent, but a whole window can: a snapshot of the window is laid over
    it in a borderless window (identical pixels, so nothing visibly changes), the change happens
    underneath, and the snapshot then fades out. Falls back to an instant change where snapshots or
    window opacity aren't available.
    """
    try:
        image = capture_window(root)
    except Exception:
        image = None
    if image is None:
        change()
        return
    cover = tk.Toplevel(root)
    cover.overrideredirect(True)
    try:
        cover.attributes("-alpha", 0.0)  # mapped and painted while invisible: no blank first frame
    except tk.TclError:
        cover.destroy()
        change()
        return
    cover.geometry(f"{root.winfo_width()}x{root.winfo_height()}+{root.winfo_rootx()}+{root.winfo_rooty()}")
    label = tk.Label(cover, image=image, bd=0, highlightthickness=0, padx=0, pady=0)
    label.image = image
    label.pack()
    cover.update()
    cover.attributes("-alpha", 1.0)  # now covers the window with the very same pixels
    cover.update()
    change()
    root.update_idletasks()  # restyle underneath while hidden
    fade = Animation(cover, lambda v: cover.attributes("-alpha", 1.0 - v))
    fade.animate_to(1.0, ms, ease_in_out, on_done=cover.destroy)


def paint_now(widget):
    """Windows only: handle pending paint messages right away.

    Windows paints uncovered areas only when nothing else is queued, so while a panel slides open the
    newly uncovered strip keeps showing stale pixels (whatever used to be there) for a frame or more.
    X11/Wayland compositors keep each window's contents, so elsewhere this is a no-op. Callers must
    cope with re-entrancy: update() can run other events, e.g. a click that restarts the animation."""
    if sys.platform == "win32":
        try:
            widget.update()
        except tk.TclError:
            pass


class Animation:
    """A value tweened over time with Tk's after(), in the spirit of Chromium's gfx::SlideAnimation.

    ``on_step(value)`` is called every frame; it may raise TclError if its widget is gone, which
    simply stops the animation. Re-targeting mid-way continues from the current value.
    """

    def __init__(self, widget, on_step, value=0.0):
        self.widget, self.on_step, self.value = widget, on_step, value
        self._job = None
        self._generation = 0  # bumped by cancel(); a frame from an older run stops itself

    @property
    def running(self):
        return self._job is not None

    def animate_to(self, target, ms, ease=ease_out, proportional=True, on_done=None):
        """Tween to ``target``. With ``proportional`` a half-finished reversal takes half the time."""
        self.cancel()
        start = self.value
        span = abs(target - start)
        if ms <= 0 or span == 0:
            if self._step(target) and on_done:
                on_done()
            return
        duration = ms / 1000 * (span if proportional else 1)
        t0 = time.perf_counter()
        generation = self._generation

        def frame():
            if generation != self._generation:
                return  # superseded by a newer animate_to/cancel (possibly during paint_now)
            self._job = None
            t = min(1.0, (time.perf_counter() - t0) / duration)
            if not self._step(start + (target - start) * ease(t)) or generation != self._generation:
                return
            if t < 1:
                self._job = self.widget.after(ANIM_FRAME_MS, frame)
            elif on_done:
                on_done()
        frame()

    def jump_to(self, value):
        self.cancel()
        self._step(value)

    def _step(self, value):
        self.value = value
        try:
            self.on_step(value)
            return True
        except tk.TclError:  # widget destroyed
            return False

    def cancel(self):
        self._generation += 1
        if self._job:
            try:
                self.widget.after_cancel(self._job)
            except tk.TclError:
                pass
            self._job = None


class RippleButton(ctk.CTkButton if ctk else object):
    """CTkButton with a ripple: a soft circle grows from the press point, covers the button and fades.

    Flicker-free by construction: the button's text is drawn on the button's own canvas, and the
    canvas sits above CTk's text label for the button's whole life. Nothing is restacked, raised
    or re-coloured during a click, so there are no X repaints, no spurious <Enter>/<Leave> events
    and no colour toggling. Tk has no transparency, so the ink is the button colour blended
    towards the text colour, with the rounded corners re-masked while it animates.
    """
    RIPPLE_MS = 600
    RIPPLE_OPACITY = 0.12    # kept low on purpose: a strong ink reads as a flash, not a ripple
    FRAME_MS = 15
    enabled = True           # class-wide; the "Reduce motion" switch turns every ripple off

    def __init__(self, *args, **kwargs):
        self._mirror_ready = False
        self._hover_anim = None
        super().__init__(*args, **kwargs)
        self._ripple_job = None
        self._ripple = None
        self._hover_anim = Animation(self, self._paint_hover)
        self._canvas.bind("<Button-1>", self._on_press, add="+")
        self._mirror_ready = True
        self._sync_text()

    # ---- hover: Chromium-style fade instead of an instant colour swap -------- #
    def _paint_hover(self, h):
        c, ap = self._canvas, self._apply_appearance_mode
        base = self._bg_color if self._fg_color == "transparent" else self._fg_color
        hover = self._hover_color if self._hover_color is not None else base
        color = _blend(_rgb(c, ap(base)), _rgb(c, ap(hover)), h)
        c.itemconfig("inner_parts", fill=color, outline=color)

    def _on_enter(self, event=None):
        self._mouse_inside = True
        if self._hover is True and self._state == "normal" and self._hover_anim is not None:
            self._hover_anim.animate_to(1.0, HOVER_MS, ease_out)  # GlowHoverController::Show: EASE_OUT

    # ---- text drawn on the canvas (the real label stays hidden underneath) ---- #
    def _sync_text(self):
        if not self._mirror_ready:
            return
        c, label = self._canvas, self._text_label
        try:
            c.delete("btn_text")
            if label is None:
                return
            if not getattr(label, "_mirrored", False):  # CTk creates the label lazily, maybe later
                label._mirrored = True
                label.bind("<Configure>", lambda e: self._sync_text(), add="+")
                tk.Misc.tkraise(c)  # once, at creation (not mapped yet); Canvas.lift() would raise items
            x, y = self._label_text_origin(label)
            c.create_text(x, y, anchor="nw", text=label.cget("text"), font=label.cget("font"),
                          fill=label.cget("fg"), justify=label.cget("justify"), tags=("btn_text", "btn_fg"))
        except tk.TclError:  # being destroyed
            pass

    def _draw(self, no_color_updates=False):
        super()._draw(no_color_updates)
        if self._hover_anim is not None and self._hover_anim.value:
            self._paint_hover(self._hover_anim.value)  # CTk's redraw resets the colour; keep the hover state
        self._sync_text()

    def configure(self, require_redraw=False, **kwargs):
        super().configure(require_redraw, **kwargs)
        self._sync_text()

    def _update_font(self):
        super()._update_font()
        self._sync_text()

    def _set_scaling(self, *args, **kwargs):
        super()._set_scaling(*args, **kwargs)
        self._sync_text()

    @staticmethod
    def _label_text_origin(label):
        """Top-left pixel where Tk would draw the label's text (integer maths, like Tk itself;
        centring on a half-pixel midpoint would shift the text by 1px)."""
        def px(option):
            return int(float(str(label.cget(option))))
        inset = px("borderwidth") + px("highlightthickness")
        x = label.winfo_x() + inset + px("padx") + (label.winfo_width() - label.winfo_reqwidth()) // 2
        y = label.winfo_y() + inset + px("pady") + (label.winfo_height() - label.winfo_reqheight()) // 2
        return x, y

    # ---- clicks ---------------------------------------------------------------- #
    def _pointer_inside(self):
        try:
            px, py = self.winfo_pointerxy()
            return (0 <= px - self.winfo_rootx() < self.winfo_width()
                    and 0 <= py - self.winfo_rooty() < self.winfo_height())
        except tk.TclError:
            return False

    def _on_leave(self, event=None):
        if self._pointer_inside():  # ignore crossings that aren't real exits
            return
        self._mouse_inside = False
        self._click_animation_running = False
        if self._hover_anim is not None:
            self._hover_anim.animate_to(0.0, HOVER_MS, ease_in)  # GlowHoverController::Hide: EASE_IN

    def _on_release(self, event=None):
        # CTkButton's own release handler swaps the button to its non-hover colour for 100 ms as a
        # "click animation". That is a hard colour flash, so it is replaced: just run the command.
        if self._pointer_inside() and self._state != tk.DISABLED and self._command is not None:
            self._command()

    def _on_press(self, event):
        self.ripple(event.x, event.y)

    # ---- the ripple -------------------------------------------------------------- #
    def ripple(self, x=None, y=None):
        """Play the ripple from (x, y) in widget pixels; from the centre when omitted."""
        if not RippleButton.enabled or self.cget("state") == "disabled":
            return
        c = self._canvas
        w, h = c.winfo_width(), c.winfo_height()
        if w < 2 or h < 2:
            return
        x = w / 2 if x is None else x
        y = h / 2 if y is None else y
        self._stop_ripple()

        inner = c.find_withtag("inner_parts")
        base = c.itemcget(inner[0], "fill") if inner else c.cget("bg")
        label = self._text_label
        ink = label.cget("fg") if label is not None else "#ffffff"
        oval = c.create_oval(x, y, x, y, outline="", fill=base, tags="ripple")
        self._mask_corners(w, h)
        c.tag_raise("btn_fg")  # text (and any drawn icon) stays above the ink
        self._ripple = dict(oval=oval, x=x, y=y, t0=time.perf_counter(),
                            radius=max(math.hypot(x - cx, y - cy) for cx in (0, w) for cy in (0, h)),
                            base=_rgb(c, base), ink=_rgb(c, ink))
        self._ripple_frame()

    def _mask_corners(self, w, h, steps=8):
        """Cover the ink that spills past the rounded corners with the background colour."""
        c = self._canvas
        r = min(self._apply_widget_scaling(self._corner_radius), w / 2, h / 2)
        if r < 1:
            return
        for cx, cy, sx, sy in ((r, r, -1, -1), (w - r, r, 1, -1), (w - r, h - r, 1, 1), (r, h - r, -1, 1)):
            arc = [(cx + sx * r * math.cos(a), cy + sy * r * math.sin(a))
                   for a in (i * math.pi / 2 / steps for i in range(steps + 1))]
            corner = (cx + sx * r, cy + sy * r)
            c.create_polygon(*corner, *[p for pt in arc for p in pt], fill=c.cget("bg"), outline="", tags="ripple")

    def _ripple_frame(self):
        st = self._ripple
        t = (time.perf_counter() - st["t0"]) * 1000 / self.RIPPLE_MS
        try:
            if t >= 1:
                self._stop_ripple()
                return
            r = st["radius"] * (1 - (1 - t) ** 3)  # ease-out: fast start, gentle finish
            # fade in over the first 20%, then fade out continuously: no sudden step, no plateau
            alpha = self.RIPPLE_OPACITY * (t / 0.2 if t < 0.2 else ((1 - t) / 0.8) ** 1.5)
            x, y = st["x"], st["y"]
            self._canvas.coords(st["oval"], x - r, y - r, x + r, y + r)
            self._canvas.itemconfigure(st["oval"], fill=_blend(st["base"], st["ink"], alpha))
            self._ripple_job = self.after(self.FRAME_MS, self._ripple_frame)
        except tk.TclError:  # the button was destroyed mid-animation
            self._ripple_job = None

    def _stop_ripple(self):
        if self._ripple_job:
            self.after_cancel(self._ripple_job)
            self._ripple_job = None
        try:
            self._canvas.delete("ripple")
        except tk.TclError:
            pass


class ChevronButton(RippleButton):
    """RippleButton whose text is followed by a drawn chevron (crisp at any size and in any font,
    unlike Unicode arrows). ``set_chevron(p)`` rotates it: 0 points down, 1 points up, and values in
    between are used to turn it smoothly while a panel animates."""
    CHEVRON_GAP, CHEVRON_HALF = 7, 5  # unscaled px

    def __init__(self, *args, **kwargs):
        self._chevron = 0.0
        super().__init__(*args, **kwargs)

    def set_chevron(self, p):
        self._chevron = p
        self._draw_chevron()

    def _sync_text(self):
        super()._sync_text()
        if self._mirror_ready and self._canvas.find_withtag("btn_text"):
            # centre text + chevron as one group instead of leaving the text centred alone
            shift = (self._apply_widget_scaling(self.CHEVRON_GAP) + 2 * self._apply_widget_scaling(self.CHEVRON_HALF)) / 2
            self._canvas.move("btn_text", -round(shift), 0)
        self._draw_chevron()

    def _draw_chevron(self):
        if not self._mirror_ready or self._text_label is None:
            return
        c = self._canvas
        try:
            c.delete("chevron")
            box = c.bbox("btn_text")
            if not box:
                return
            s = self._apply_widget_scaling(self.CHEVRON_HALF)
            cx = box[2] + self._apply_widget_scaling(self.CHEVRON_GAP) + s
            cy = (box[1] + box[3]) / 2
            a = math.pi * self._chevron
            ca, sa = math.cos(a), math.sin(a)
            pts = []
            for x, y in ((-s, -s / 2), (0, s / 2), (s, -s / 2)):  # a "v", rotated by a
                pts += [cx + x * ca - y * sa, cy + x * sa + y * ca]
            c.create_line(*pts, fill=self._text_label.cget("fg"), width=self._apply_widget_scaling(2),
                          capstyle="round", joinstyle="round", tags=("chevron", "btn_fg"))
        except tk.TclError:
            pass


class GlideSwitch(ctk.CTkSwitch if ctk else object):
    """CTkSwitch whose knob glides and whose track colour blends from off to on, with a hover fade,
    instead of everything jumping in a single frame."""
    GLIDE_MS = 220

    def __init__(self, *args, **kwargs):
        self._glide = self._hover_fade = None
        super().__init__(*args, **kwargs)
        self._glide = Animation(self, lambda v: self._draw(no_color_updates=True), 1.0 if self._check_state else 0.0)
        self._hover_fade = Animation(self, lambda v: self._paint_glide_colors())

    def set(self, state, from_variable_callback=False):
        self._check_state = state
        if self._glide is None:
            self._draw(no_color_updates=True)
        elif self.winfo_ismapped():
            self._glide.animate_to(1.0 if state else 0.0, self.GLIDE_MS, fast_out_slow_in)
        else:  # e.g. restoring settings before the window shows: no animation needed
            self._glide.jump_to(1.0 if state else 0.0)
        if self._variable is not None and not from_variable_callback:
            self._variable_callback_blocked = True
            self._variable.set(self._onvalue if self._check_state else self._offvalue)
            self._variable_callback_blocked = False

    def _draw(self, no_color_updates=False):
        super()._draw(no_color_updates)  # CTk draws the knob at 0 or 1 ...
        if self._glide is None:
            return
        s = self._apply_widget_scaling
        args = (s(self._switch_width), s(self._switch_height), s(self._corner_radius), s(self._border_width),
                s(self._button_length), s(self._corner_radius))
        # ... and it is moved to the animated position in the same callback, so that's never shown
        if self._draw_engine.draw_rounded_slider_with_border_and_button(*args, self._glide.value, "w"):
            super()._draw(False)  # colour parts the engine just created
            self._draw_engine.draw_rounded_slider_with_border_and_button(*args, self._glide.value, "w")
        self._paint_glide_colors()

    def _paint_glide_colors(self):
        if self._glide is None:
            return
        c, ap = self._canvas, self._apply_appearance_mode
        off = _rgb(c, ap(self._fg_color))
        on = off if self._progress_color == "transparent" else _rgb(c, ap(self._progress_color))
        track = _blend(off, on, self._glide.value)
        c.itemconfig("progress_parts", fill=track, outline=track)
        knob = _blend(_rgb(c, ap(self._button_color)), _rgb(c, ap(self._button_hover_color)), self._hover_fade.value)
        c.itemconfig("slider_parts", fill=knob, outline=knob)

    def _on_enter(self, event=0):
        if self._hover is True and self._state == "normal" and self._hover_fade is not None:
            self._hover_state = True
            self._hover_fade.animate_to(1.0, HOVER_MS, ease_out)

    def _on_leave(self, event=0):
        self._hover_state = False
        if self._hover_fade is not None:
            self._hover_fade.animate_to(0.0, HOVER_MS, ease_in)


class GlideOptionMenu(ctk.CTkOptionMenu if ctk else object):
    """CTkOptionMenu whose hover colour fades in and out with Chromium's timing instead of switching
    in a single frame. (The opened list is a native Tk menu, so its rows can't be animated.)"""

    def __init__(self, *args, **kwargs):
        self._hover_fade = None
        super().__init__(*args, **kwargs)
        self._hover_fade = Animation(self, self._paint_hover)

    def _paint_hover(self, h):
        c, ap = self._canvas, self._apply_appearance_mode
        color = _blend(_rgb(c, ap(self._button_color)), _rgb(c, ap(self._button_hover_color)), h)
        c.itemconfig("inner_parts_right", fill=color, outline=color)

    def _pointer_inside(self):
        try:
            px, py = self.winfo_pointerxy()
            return (0 <= px - self.winfo_rootx() < self.winfo_width()
                    and 0 <= py - self.winfo_rooty() < self.winfo_height())
        except tk.TclError:
            return False

    def _on_enter(self, event=0):
        self._close_on_next_click = self._dropdown_menu.is_open()
        if self._hover is True and self._state == tk.NORMAL and len(self._values) > 0 and self._hover_fade:
            self._hover_fade.animate_to(1.0, HOVER_MS, ease_out)

    def _on_leave(self, event=0):
        # moving between the menu's canvas and its text label isn't leaving the widget
        if self._hover_fade and not self._pointer_inside():
            self._hover_fade.animate_to(0.0, HOVER_MS, ease_in)

    def _draw(self, no_color_updates=False):
        super()._draw(no_color_updates)
        if self._hover_fade is not None and self._hover_fade.value:
            self._paint_hover(self._hover_fade.value)


class GlideSegments(ctk.CTkFrame if ctk else object):
    """Segmented control drawn on one canvas, in the style of Chromium's tab strip:

    * the selected pill glides to its new segment (FAST_OUT_SLOW_IN), it doesn't jump
    * hovering a segment fades its highlight in over 200 ms (EASE_OUT) and out (EASE_IN), like
      Chromium's GlowHoverController, with a soft radial glow that follows the pointer
    * all shapes are on one double-buffered canvas with antialiased corners

    Drop-in for the parts of CTkSegmentedButton the app uses: values, command(value), set(), get().
    """
    PAD, CORNER = 3, 6            # inset of segments in the bar, and segment corner radius (unscaled)
    SEG_PAD_X, MIN_SEG_W = 16, 56
    GLIDE_MS = 260
    GLOW_ALPHA, GLOW_RINGS = 0.16, 8   # kept gentle; Chromium's "subtle" glow peaks at 0.45

    def __init__(self, master, values, command=None, height=30, font=None):
        self._ready = False
        self._values, self._command = list(values), command
        self._font = font or ctk.CTkFont()
        probe = tkinter.font.Font(family=self._font.cget("family"), size=-abs(self._font.cget("size")),
                                  weight=self._font.cget("weight"))
        self._seg_w = [max(self.MIN_SEG_W, probe.measure(v) + 2 * self.SEG_PAD_X) for v in self._values]
        self._h = height
        super().__init__(master, width=sum(self._seg_w) + 2 * self.PAD, height=height,
                         fg_color="transparent", corner_radius=0)
        self._theme = ctk.ThemeManager.theme["CTkSegmentedButton"]
        self._cv = ctk.CTkCanvas(self, highlightthickness=0, cursor="hand2")
        self._cv.place(x=0, y=0, relwidth=1, relheight=1)
        self._selected = 0
        self._hovered = None
        self._glow_x = {}
        self._hover = [Animation(self, lambda v, i=i: self._paint_segment(i)) for i in range(len(self._values))]
        self._pill_anim = Animation(self, self._pill_step)
        self._pill_from = self._pill_to = None
        self._cv.bind("<Motion>", self._on_motion)
        self._cv.bind("<Leave>", self._on_leave_bar)
        self._cv.bind("<ButtonPress-1>", self._on_click)
        self._ready = True
        self._render()

    # ---- public API ------------------------------------------------------------ #
    def get(self):
        return self._values[self._selected]

    def set(self, value, animate=True):
        i = self._values.index(value)
        if i == self._selected:
            return
        old, self._selected = self._selected, i
        if self._hover[i].value:  # Chromium: the active tab has no hover highlight
            self._hover[i].animate_to(0.0, HOVER_MS, ease_in)
        self._pill_from, self._pill_to = self._pill_x, self._segment_box(i)[::2]
        if animate and self.winfo_ismapped():
            self._pill_anim.value = 0.0
            self._pill_anim.animate_to(1.0, self.GLIDE_MS, fast_out_slow_in, proportional=False)
        else:
            self._pill_anim.jump_to(1.0)
        self._paint_segment(old)

    # ---- geometry ----------------------------------------------------------------- #
    def _scale(self):
        return self._get_widget_scaling()

    def _segment_box(self, i):
        s = self._scale()
        x0 = (self.PAD + sum(self._seg_w[:i])) * s
        return x0, self.PAD * s, x0 + self._seg_w[i] * s, (self._h - self.PAD) * s

    def _segment_at(self, x):
        for i in range(len(self._values)):
            x0, _, x1, _ = self._segment_box(i)
            if x0 <= x < x1:
                return i
        return None

    # ---- drawing ---------------------------------------------------------------------- #
    def _color(self, key):
        return self._apply_appearance_mode(self._theme[key])

    def _rrect(self, tag, x0, y0, x1, y1, r, color):
        cv = self._cv
        r = max(1, round(r))
        for cx, cy in ((x0 + r, y0 + r), (x1 - r, y0 + r), (x0 + r, y1 - r), (x1 - r, y1 - r)):
            cv.create_aa_circle(cx, cy, r, fill=color, tags=(tag, tag + "_circle"))
        cv.create_rectangle(x0 + r, y0, x1 - r, y1, fill=color, outline="", width=0, tags=(tag, tag + "_rect"))
        cv.create_rectangle(x0, y0 + r, x1, y1 - r, fill=color, outline="", width=0, tags=(tag, tag + "_rect"))

    def _move_rrect(self, tag, x0, y0, x1, y1, r):
        cv = self._cv
        r = max(1, round(r))
        circles, rects = cv.find_withtag(tag + "_circle"), cv.find_withtag(tag + "_rect")
        for cid, (cx, cy) in zip(circles, ((x0 + r, y0 + r), (x1 - r, y0 + r), (x0 + r, y1 - r), (x1 - r, y1 - r))):
            cv.coords(cid, cx, cy)
        cv.coords(rects[0], x0 + r, y0, x1 - r, y1)
        cv.coords(rects[1], x0, y0 + r, x1, y1 - r)

    def _render(self):
        """Full redraw (on creation, theme change or rescale)."""
        if not self._ready:
            return
        cv, s = self._cv, self._scale()
        cv.delete("all")
        cv.configure(bg=self._apply_appearance_mode(self._bg_color))
        w, h = (sum(self._seg_w) + 2 * self.PAD) * s, self._h * s
        self._rrect("bar", 0, 0, w, h, (self.CORNER + self.PAD) * s, self._color("fg_color"))
        for i in range(len(self._values)):
            x0, y0, x1, y1 = self._segment_box(i)
            self._rrect(f"seg{i}", x0, y0, x1, y1, self.CORNER * s, self._color("unselected_color"))
            for k in range(self.GLOW_RINGS):
                cv.create_oval(0, 0, 0, 0, outline="", fill="", tags=(f"glow{i}", f"glow{i}_{k}"))
        x0, y0, x1, y1 = self._segment_box(self._selected)
        self._pill_x = (x0, x1)
        self._rrect("pill", x0, y0, x1, y1, self.CORNER * s, self._color("selected_color"))
        font = (self._font.cget("family"), -round(abs(self._font.cget("size")) * s), self._font.cget("weight"))
        for i, v in enumerate(self._values):
            x0, y0, x1, y1 = self._segment_box(i)
            cv.create_text((x0 + x1) / 2, (y0 + y1) / 2, text=v, font=font, fill=self._color("text_color"), tags="text")
        for i in range(len(self._values)):
            self._paint_segment(i)

    def _draw(self, no_color_updates=False):
        super()._draw(no_color_updates)
        self._render()  # theme or scaling changed

    def _paint_segment(self, i):
        cv, s = self._cv, self._scale()
        h = self._hover[i].value
        base = _rgb(cv, self._color("unselected_color"))
        seg = _blend(base, _rgb(cv, self._color("unselected_hover_color")), h)
        cv.itemconfig(f"seg{i}", fill=seg)
        if i == self._selected:
            pill = _blend(_rgb(cv, self._color("selected_color")), _rgb(cv, self._color("selected_hover_color")), h)
            cv.itemconfig("pill", fill=pill)
        # radial glow: concentric ellipses blending towards white, following the pointer
        x0, y0, x1, y1 = self._segment_box(i)
        rx, ry = min((x1 - x0) / 2 - self.CORNER * s / 2, (y1 - y0) * 1.6), (y1 - y0) / 2
        gx = min(max(self._glow_x.get(i, (x0 + x1) / 2), x0 + rx + self.CORNER * s / 2), x1 - rx - self.CORNER * s / 2)
        seg_rgb, white = _rgb(cv, seg), (255, 255, 255)
        for k in range(self.GLOW_RINGS):
            f = 1 - k / self.GLOW_RINGS  # outer ring first
            alpha = self.GLOW_ALPHA * h * (k + 1) / self.GLOW_RINGS
            color = _blend(seg_rgb, white, alpha) if h > 0.01 else ""
            cv.coords(f"glow{i}_{k}", gx - rx * f, (y0 + y1) / 2 - ry * f, gx + rx * f, (y0 + y1) / 2 + ry * f)
            cv.itemconfig(f"glow{i}_{k}", fill=color)
        cv.tag_raise("pill")
        cv.tag_raise("text")

    def _pill_step(self, v):
        if self._pill_from is None:
            return
        s = self._scale()
        (a0, a1), (b0, b1) = self._pill_from, self._pill_to
        x0, x1 = a0 + (b0 - a0) * v, a1 + (b1 - a1) * v
        self._pill_x = (x0, x1)
        _, y0, _, y1 = self._segment_box(0)
        self._move_rrect("pill", x0, y0, x1, y1, self.CORNER * s)
        self._paint_segment(self._selected)

    # ---- events --------------------------------------------------------------------- #
    def _on_motion(self, e):
        i = self._segment_at(e.x)
        if i is not None:
            self._glow_x[i] = e.x
        if i != self._hovered:
            if self._hovered is not None:
                self._hover[self._hovered].animate_to(0.0, HOVER_MS, ease_in)
            self._hovered = i
            if i is not None and i != self._selected:
                self._hover[i].animate_to(1.0, HOVER_MS, ease_out)
        elif i is not None:
            self._paint_segment(i)  # glow follows the pointer

    def _on_leave_bar(self, e):
        if self._hovered is not None:
            self._hover[self._hovered].animate_to(0.0, HOVER_MS, ease_in)
        self._hovered = None

    def _on_click(self, e):
        i = self._segment_at(e.x)
        if i is None or i == self._selected:
            return
        self.set(self._values[i])
        if self._command:
            self._command(self._values[i])


class GlideTabview(ctk.CTkFrame if ctk else object):
    """Tab view with a GlideSegments tab strip; switching slides the new page in over the old one
    (from the side of the chosen tab), so the content never swaps in a single frame.

    Only ONE window moves per frame and the old page stays still underneath. Moving both pages made
    the X server briefly overlap them and repaint ~75% of the old page during a slide, a flicker
    risk; a single moving window is shifted by the server without any repaint.
    API-compatible with how the app used CTkTabview."""
    SLIDE_MS = 280

    def __init__(self, master, names):
        super().__init__(master, fg_color="transparent", corner_radius=0)
        self._names = list(names)
        self.strip = GlideSegments(self, self._names, command=self.set)
        self.strip.pack(pady=(0, 6))
        self.body = ctk.CTkFrame(self, fg_color=ctk.ThemeManager.theme["CTkFrame"]["fg_color"], corner_radius=10)
        self.body.pack(fill="both", expand=True)
        # inset by the corner radius so sliding pages never cover the body's rounded corners
        self.clip = ctk.CTkFrame(self.body, fg_color="transparent", corner_radius=0)
        self.clip.pack(fill="both", expand=True, padx=6, pady=6)
        self._pages = {n: ctk.CTkFrame(self.clip, fg_color="transparent", corner_radius=0) for n in self._names}
        self._current = self._names[0]
        self._pages[self._current].place(x=0, y=0, relwidth=1, relheight=1)
        self._slide = Animation(self, self._slide_step)
        self._sliding = None
        self.on_show = None  # optional callback(name), called as a page starts to appear

    def tab(self, name):
        return self._pages[name]

    def get(self):
        return self._current

    def set(self, name, animate=True):
        if name == self._current:
            return
        self.strip.set(name, animate=animate)
        if self._sliding:  # a new switch while sliding: settle the previous one first
            self._slide.cancel()
            self._end_slide()
        old, new = self._pages[self._current], self._pages[name]
        direction = 1 if self._names.index(name) > self._names.index(self._current) else -1
        self._current = name
        if self.on_show:
            self.on_show(name)
        if not animate or not self.winfo_ismapped():
            old.place_forget()
            new.place(x=0, y=0, relwidth=1, relheight=1)
            return
        width = self.clip.winfo_width() / self._get_widget_scaling()  # place() x is in unscaled units
        self._sliding = (old, new, direction, width)
        new.place(x=direction * width, y=0, relwidth=1, relheight=1)  # parked just outside the clip
        tk.Misc.tkraise(new)  # above the old page; done while it's still out of view
        self._slide.value = 0.0
        self._slide.animate_to(1.0, self.SLIDE_MS, fast_out_slow_in, proportional=False, on_done=self._end_slide)

    def _slide_step(self, v):
        if not self._sliding:
            return
        _, new, d, width = self._sliding
        new.place(x=d * (width - round(width * v)), y=0, relwidth=1, relheight=1)
        paint_now(self)  # Windows: paint the page as it is uncovered, not a frame later

    def _end_slide(self):
        if self._sliding:
            old, new, _, _ = self._sliding
            self._sliding = None
            old.place_forget()
            new.place(x=0, y=0, relwidth=1, relheight=1)


class EntryEditing:
    """The text-editing shortcuts people expect, which Tk's Entry lacks (on Linux it even maps Ctrl+A to
    Emacs "start of line"): Ctrl+A select all, Ctrl+Z / Ctrl+Y / Ctrl+Shift+Z undo-redo,
    Ctrl+Backspace / Ctrl+Delete delete a word, and paste replacing the selection.

    Works through a bindtag placed in front of the Entry class bindings, so Tk's own behaviour
    (word jumps, Shift+arrows, Home/End, cut/copy, double-click word select) is untouched.
    """
    TAG = "UltraCalcEditing"
    COALESCE_S = 1.0   # keystrokes of the same kind within this gap are undone together
    MAX_UNDO = 200

    def __init__(self, entry):
        self.entry = entry
        self.undo, self.redo = [], []
        self._last_kind, self._last_t = None, 0.0
        tags = list(entry.bindtags())
        if self.TAG not in tags:
            tags.insert(tags.index("Entry") if "Entry" in tags else 1, self.TAG)
            entry.bindtags(tuple(tags))
        entry._editing = self

    @classmethod
    def install(cls, root):
        """Add the shortcuts to every Entry under ``root``."""
        root.bind_class(cls.TAG, "<KeyPress>", cls._on_key)
        root.bind_class(cls.TAG, "<ButtonPress>", cls._break_group)  # clicking elsewhere starts a new step
        stack = [root]
        while stack:
            w = stack.pop()
            if isinstance(w, tk.Entry) and not hasattr(w, "_editing"):
                cls(w)
            stack += w.winfo_children()

    # ---- undo history ------------------------------------------------------ #
    def snapshot(self, kind):
        """Remember the text before a change. Typing/deleting runs are grouped into one undo step."""
        now = time.monotonic()
        state = (self.entry.get(), self.entry.index("insert"))
        grouped = (kind in ("type", "delete") and kind == self._last_kind and now - self._last_t < self.COALESCE_S
                   and not self.entry.selection_present())  # replacing a selection is its own step
        self._last_kind, self._last_t = kind, now
        if grouped or (self.undo and self.undo[-1][0] == state[0]):
            return
        self.undo.append(state)
        del self.undo[:-self.MAX_UNDO]
        self.redo.clear()

    def _restore(self, src, dst):
        current = (self.entry.get(), self.entry.index("insert"))
        while src and src[-1][0] == current[0]:  # skip snapshots of keys that changed nothing
            src.pop()
        if not src:
            return
        dst.append(current)
        text, pos = src.pop()
        self.entry.delete(0, "end")
        self.entry.insert(0, text)
        self.entry.icursor(pos)
        self.entry.selection_clear()
        self._last_kind = None

    def undo_step(self):
        self._restore(self.undo, self.redo)

    def redo_step(self):
        self._restore(self.redo, self.undo)

    # ---- editing helpers ----------------------------------------------------- #
    def _delete_selection(self):
        if self.entry.selection_present():
            self.entry.delete("sel.first", "sel.last")
            return True
        return False

    def _delete_word(self, forward):
        if self._delete_selection():
            return
        text, pos = self.entry.get(), self.entry.index("insert")
        is_word = lambda ch: ch.isalnum() or ch == "_"
        i, step = pos, (1 if forward else -1)
        peek = (lambda k: text[k]) if forward else (lambda k: text[k - 1])
        inside = (lambda k: k < len(text)) if forward else (lambda k: k > 0)
        while inside(i) and peek(i).isspace():
            i += step
        if inside(i) and is_word(peek(i)):
            while inside(i) and is_word(peek(i)):
                i += step
        elif inside(i):
            i += step  # a single operator/bracket
        self.entry.delete(min(i, pos), max(i, pos))

    @staticmethod
    def _break_group(e):
        ed = getattr(e.widget, "_editing", None)
        if ed is not None:
            ed._last_kind = None

    _MOVES = frozenset(("Left", "Right", "Up", "Down", "Home", "End", "Prior", "Next"))

    @staticmethod
    def _on_key(e):
        ed = getattr(e.widget, "_editing", None)
        if ed is None:
            return None
        ctrl, shift = e.state & 0x4, e.state & 0x1
        if e.keysym in EntryEditing._MOVES:  # moving the cursor ends a typing run
            ed._last_kind = None
            return None
        if ctrl:
            k = e.keysym.lower()
            if k == "a":
                e.widget.selection_range(0, "end")
                e.widget.icursor("end")
                ed._last_kind = None
                return "break"
            if k == "z":
                ed.redo_step() if shift else ed.undo_step()
                return "break"
            if k == "y":
                ed.redo_step()
                return "break"
            if k in ("backspace", "delete"):
                ed.snapshot("word")
                ed._delete_word(forward=k == "delete")
                return "break"
            if k == "v":
                ed.snapshot("paste")
                ed._delete_selection()  # Tk on X11 would insert next to the selection instead
            elif k == "x":
                ed.snapshot("cut")
            return None
        if e.keysym == "Insert" and shift:  # Shift+Insert paste
            ed.snapshot("paste")
            ed._delete_selection()
        elif e.keysym in ("BackSpace", "Delete"):
            ed.snapshot("delete")
        elif e.char and e.char.isprintable() and not e.state & 0x8:  # 0x8 = Alt
            ed.snapshot("type")
        return None


# keys typed into the calculator entry -> keypad button that should ripple
KEY_TO_BUTTON = {"*": "×", "/": "÷", "-": "−", "^": "xʸ", "!": "n!", "BackSpace": "⌫"}

# fonts known to contain "⌫"; the first one installed is used, otherwise the key reads "DEL"
BACKSPACE_FONTS = ("Adwaita Sans", "Segoe UI Symbol", "Apple Symbols", "DejaVu Sans", "Noto Sans Symbols",
                   "Noto Sans Symbols 2", "FreeSerif", "FreeMono", "Symbola")
TAB_NAMES = ("Calculator", "Graph", "Tools", "Challenge")
KEY_HEIGHT, KEY_PAD = 40, 2              # keypad button height and grid padding (unscaled px)
SCI_ROWS = 4
SCI_PANEL_H = SCI_ROWS * (KEY_HEIGHT + 2 * KEY_PAD)  # full height of the scientific panel
SCI_ANIM_MS = 300                        # open/close "swoop" duration
ANIM_FRAME_MS = 15
RESULT_FONT_MAX, RESULT_FONT_MIN = 42, 16

FUNCTION_HELP = [
    ("sin(x)  cos(x)  tan(x)", "trig, in DEG or RAD (header switch); graph & calculus use RAD"),
    ("asin(x) acos(x) atan(x)", "inverse trig"),
    ("sinh(x) cosh(x) tanh(x)", "hyperbolic functions"),
    ("sqrt(x)  cbrt(x)  root(x, n)", "square, cube and n-th root   (also √x, ∛x)"),
    ("abs(x)  sign(x)", "absolute value, sign (-1, 0, 1)"),
    ("log(x)  ln(x)  log2(x)  logb(x, b)", "log base 10, natural log, base 2, base b"),
    ("exp(x)  pow(a, b)", "e^x, a^b"),
    ("floor(x) ceil(x) round(x, n)", "rounding; round is half away from zero"),
    ("fact(n)  n!", "factorial (non-integers use the gamma function)"),
    ("ncr(n, r)  npr(n, r)", "combinations, permutations"),
    ("gcd(a, b)  lcm(a, b)", "greatest common divisor, least common multiple"),
    ("isprime(n)  nextprime(n)", "1 if prime else 0; next prime after n"),
    ("fib(n)", "n-th Fibonacci number"),
    ("hypot(a, b)  rad(x)  deg(x)", "√(a²+b²); degrees→radians; radians→degrees"),
    ("mean median stdev sum max min", "take any number of values: mean(1, 2, 3)"),
    ("rand()  randint(a, b)", "random number in [0, 1); random integer in [a, b]"),
]


def pretty_expr(s: str) -> str:
    """Display form of what the user typed: 12*7 -> 12 × 7, 2**3 -> 2^3."""
    s = s.replace("**", "^")
    s = re.sub(r"(?<!/)/(?!/)", "÷", s).replace("*", "×")
    s = re.sub(r"\s*(<=|>=|==|<>|:=|[≠≤≥=<>])\s*", r" \1 ", s)
    return re.sub(r"\s*(×|÷|(?<![eE])\+)\s*", r" \1 ", s).strip()


def group_digits(text: str) -> str:
    """1234567.5 -> 1,234,567.5 for display; anything that isn't a plain number is left alone."""
    m = re.fullmatch(r"(-?)(\d{4,})(\.\d+)?", text)
    return f"{m.group(1)}{int(m.group(2)):,}{m.group(3) or ''}" if m else text


def _write_json_atomic(path: str, data):
    tmp = path + ".tmp"
    try:
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False)
        os.replace(tmp, path)  # atomic: never leaves a half-written file
    except OSError:
        pass


def load_settings() -> dict:
    try:
        with open(SETTINGS_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
        return data if isinstance(data, dict) else {}
    except (OSError, ValueError):
        return {}


# --------------------------------------------------------------------------- #
#  The app
# --------------------------------------------------------------------------- #
class UltraCalc(ctk.CTk if ctk else object):
    def __init__(self, settings: dict | None = None):
        settings = load_settings() if settings is None else settings
        # set the theme before any window exists, so a light-mode user never sees a dark frame first
        ctk.set_appearance_mode("light" if settings.get("theme") == "light" else "dark")
        super().__init__()
        self.title("UltraCalc")
        self.minsize(1000, 700)
        geometry = settings.get("geometry", "")
        m = re.fullmatch(r"(\d+)x(\d+)", geometry if isinstance(geometry, str) else "")
        self.geometry(geometry if m and int(m.group(1)) >= 1000 and int(m.group(2)) >= 700 else "1160x860")

        self.engine = Engine()
        self.quiz_engine = Engine()
        self.history = []
        self.hist_idx = None
        self.last_text = ""
        self._pl = None
        self._plot_job = None
        self._save_job = None
        self._hist_widgets = []  # newest first
        self._keypad = {}        # button label -> calculator button, for keyboard ripples
        self._drag = None        # graph panning state
        self._help_win = None
        self._dialog_open = False     # a native Save dialog is showing (don't open a second one)
        self._last_save_dir = None    # where the last save went; the next dialog starts there
        self._theme_busy_until = 0.0  # monotonic time until which a theme blend is running
        self._theme_redraw_s = 0.35   # last measured theme redraw time (sizes the blend's hold)

        self.grid_columnconfigure(0, weight=1)
        self.grid_rowconfigure(1, weight=1)

        self._build_header()
        self.tabs = GlideTabview(self, TAB_NAMES)
        self.tabs.grid(row=1, column=0, sticky="nsew", padx=(10, 6), pady=(0, 10))
        self._build_calc_tab()
        self._build_graph_tab()
        self._build_tools_tab()
        self._build_challenge_tab()
        self._build_sidebar()

        self._apply_settings(settings)
        self._load_history()
        self._bind_shortcuts()
        EntryEditing.install(self)
        self.tabs.on_show = lambda name: name == "Graph" and self._mpl is None and self.plot()
        # import Matplotlib in the background so the first visit to the Graph tab doesn't stall; started
        # after the window is up, because importing during startup competes with building the window
        self.after(1500, lambda: threading.Thread(target=_preload_matplotlib, daemon=True).start())
        self.protocol("WM_DELETE_WINDOW", self._on_close)
        self.after(150, self.entry.focus_set)
        self.after(250, self.plot)

    # ================= settings ============================================ #
    def _apply_settings(self, s: dict):
        self.engine.import_state(s.get("engine") or {})
        self.angle.set("DEG" if self.engine.deg else "RAD")
        if s.get("theme") == "light":
            self.theme_sw.select()
        if s.get("reduce_motion"):
            self.motion_sw.select()
        self._toggle_motion(save=False)
        self.set_scientific(s.get("scientific") is not False, animate=False)
        self._refresh_mem()
        self._refresh_vars()

    def _settings_snapshot(self) -> dict:
        size = self.geometry().split("+")[0]  # CTk reports unscaled units, so HiDPI sizes don't grow
        return {"version": 1, "theme": "light" if self.theme_sw.get() else "dark",
                "scientific": self._sci_open, "reduce_motion": bool(self.motion_sw.get()),
                "geometry": size, "engine": self.engine.export_state()}

    # ================= keyboard shortcuts =================================== #
    def _bind_shortcuts(self):
        for seq, fn in (("<Control-l>", self._sc_clear), ("<Control-L>", self._sc_clear),
                        ("<Control-c>", self._sc_copy), ("<Control-C>", self._sc_copy),
                        ("<Control-s>", self._sc_save), ("<Control-S>", self._sc_save),
                        ("<F1>", lambda e: self.show_help())):
            self.bind(seq, fn)
        for i, name in enumerate(TAB_NAMES, 1):
            self.bind(f"<Control-Key-{i}>", lambda e, n=name: self._goto_tab(n))

    def _goto_tab(self, name):
        self.tabs.set(name)
        if name == "Calculator":
            self.entry.focus_set()
        elif name == "Graph":
            self.g_f.focus_set()
        return "break"

    def _sc_clear(self, e=None):
        self._goto_tab("Calculator")
        self.clear()
        return "break"

    def _sc_save(self, e=None):
        if self.tabs.get() == "Graph":
            self.export_graph()
        return "break"

    def _sc_copy(self, e=None):
        """Ctrl+C copies the result unless some other text is selected (then it's a normal copy)."""
        w = self.focus_get()
        if isinstance(w, tk.Entry) and (w.selection_present() or w is not self.entry._entry):
            return None
        if self.tabs.get() == "Calculator":
            self._copy_result()
        return "break"

    def show_help(self):
        if self._help_win is not None and self._help_win.winfo_exists():
            self._help_win.lift()
            self._help_win.focus_set()
            return
        win = self._help_win = ctk.CTkToplevel(self)
        win.title("UltraCalc reference")
        win.geometry("700x640")
        box = ctk.CTkTextbox(win, font=ctk.CTkFont(family=MONO, size=13), wrap="word")
        box.pack(fill="both", expand=True, padx=10, pady=10)
        lines = ["FUNCTIONS"] + [f"  {sig:<36} {desc}" for sig, desc in FUNCTION_HELP]
        if self.engine.user_funcs:
            lines += ["", "YOUR FUNCTIONS"] + [f"  {f.signature:<36} = {f.body}" for f in self.engine.user_funcs.values()]
        lines += ["", "OPERATORS",
                  "  + − × ÷   ^ (power)   // (floor div)   mod   n!   20% (= 0.2)",
                  "  2x, 3pi, 2(1+1)      implicit multiplication",
                  "", "CONSTANTS & NAMES",
                  "  pi  e  tau  phi      ans (last result)   m (memory)",
                  "", "DEFINING THINGS",
                  "  x := 7   or   let x = 7              variable",
                  "  f(x) := x^2 + 1   or   let f(x) = …  function (several parameters: g(a, b) := a*b)",
                  "", "CHECKING ANSWERS",
                  "  1+1=11  →  ✘ Wrong      5!=120  →  ✔ Correct      also < > <= >= ≠ and chains: 1 < 2 <= 2",
                  "", "SHORTCUTS",
                  "  Enter         evaluate            Esc       clear entry",
                  "  ↑ / ↓         browse history      Ctrl+L    clear and go to calculator",
                  "  Ctrl+C        copy result (when no text is selected)",
                  "  Ctrl+1…4      switch tabs         F1        this reference",
                  "  Ctrl+S        save the graph (on the Graph tab)",
                  "", "GRAPH  (modes: y = f(x) · Polar · Parametric · 3D)",
                  "  y = f(x):    sin(x); x^2/10      scroll = zoom, drag = pan, double-click = reset",
                  "               log x / log y switches for logarithmic axes (e.g. exp(x), x^3 over 0.01 … 100)",
                  "  Save… or Ctrl+S: export as PNG, SVG or PDF (the GPU 3D view saves as PNG)",
                  "  Polar:       r(θ) = cos(4θ)      write θ as θ, theta or t",
                  "  Parametric:  x(t), y(t) = sin(3t), sin(2t)      ';' between curves",
                  "  3D:          z(x, y) = sin(x)*cos(y)      drag = rotate, right-drag = zoom",
                  "  Surface:     x, y, z (u, v) = cos(u)sin(v), sin(u)sin(v), cos(v)      (a sphere)",
                  "  Implicit:    x^2 + y^2 + z^2 = 1      min(A, B) = join, max(A, B) = overlap, max(A, -B) = carve",
                  "  3D shapes save as STL models (Save… / Ctrl+S) for Blender, 3D printing or CAD",
                  "  your own functions work in every mode: f(x)"]
        box.insert("1.0", "\n".join(lines))
        box.configure(state="disabled")
        text = box._textbox  # Tk's Text maps Ctrl+A to "start of line"; make it select all
        text.bind("<Control-a>", lambda e: (text.tag_add("sel", "1.0", "end-1c"), "break")[1])
        win.bind("<Escape>", lambda e: win.destroy())
        win.after(100, win.focus_set)

    # ================= header ============================================== #
    def _build_header(self):
        h = ctk.CTkFrame(self, fg_color="transparent")
        h.grid(row=0, column=0, columnspan=2, sticky="ew", padx=12, pady=(10, 4))
        ctk.CTkLabel(h, text="🧮 UltraCalc", font=ctk.CTkFont(size=24, weight="bold")).pack(side="left")
        self.theme_sw = GlideSwitch(h, text="Light mode", command=self._toggle_theme)
        self.theme_sw.pack(side="right", padx=(12, 0))
        self.motion_sw = GlideSwitch(h, text="No flashing", command=self._toggle_motion)
        self.motion_sw.pack(side="right", padx=12)
        self.angle = GlideSegments(h, ["DEG", "RAD"], command=self._set_angle)
        self.angle.pack(side="right", padx=12)

    def _toggle_theme(self):
        self._schedule_save()
        # let the switch knob finish gliding, then dissolve the whole window into the new theme
        self.after(GlideSwitch.GLIDE_MS + 30, self._apply_theme_smoothly)

    def _apply_theme_smoothly(self):
        mode = "light" if self.theme_sw.get() else "dark"
        if ctk.get_appearance_mode().lower() == mode:
            return
        wait = self._theme_busy_until - time.monotonic()
        if wait > 0:  # a blend is still running; KWin would ignore a new one and the swap would be instant
            self.after(int(wait * 1000) + 20, self._apply_theme_smoothly)
            return

        def apply():
            t0 = time.perf_counter()
            ctk.set_appearance_mode(mode)
            self.plot()  # repaint the graph now, while the old frame is still shown
            self.update_idletasks()
            self._theme_redraw_s = time.perf_counter() - t0

        # hold the old frame a bit longer than the redraw takes, so the blend never shows a half-redraw
        delay = min(800, max(250, self._theme_redraw_s * 1300 + 80))
        if kwin_blend_available() and kwin_blend(delay):
            apply()
            self._theme_busy_until = time.monotonic() + (delay + 450) / 1000
        else:
            crossfade_window(self, apply)
            self._theme_busy_until = time.monotonic() + (THEME_FADE_MS + 100) / 1000

    # ---- scientific panel: slides open/closed like a phone calculator ---------- #
    def toggle_scientific(self):
        self.set_scientific(not self._sci_open)
        self._schedule_save()

    def set_scientific(self, open_, animate=True):
        self._sci_open = open_
        if self._sci_job:
            self.after_cancel(self._sci_job)
            self._sci_job = None
        target = 1.0 if open_ else 0.0
        if not animate:
            self._set_sci_progress(target)
            return
        start, t0 = self._sci_p, time.perf_counter()
        duration = SCI_ANIM_MS / 1000 * abs(target - start)  # reversing mid-way takes only the rest
        self._sci_generation += 1
        generation = self._sci_generation

        def frame():
            if generation != self._sci_generation:
                return  # a newer toggle took over (e.g. a click handled inside paint_now)
            t = min(1.0, (time.perf_counter() - t0) / duration) if duration > 0 else 1.0
            # opening swoops in (fast, then settles); closing eases in and out
            eased = 1 - (1 - t) ** 3 if open_ else t * t * (3 - 2 * t)
            self._set_sci_progress(start + (target - start) * eased)
            paint_now(self)  # Windows: paint the newly uncovered strip now, not a frame later
            if generation == self._sci_generation:
                self._sci_job = self.after(ANIM_FRAME_MS, frame) if t < 1 else None
        frame()

    def _set_sci_progress(self, p):
        """0 = hidden, 1 = fully open. The panel slides down inside a clip whose height grows,
        so the rows below glide along with it."""
        self._sci_p = p
        self.sci_toggle.set_chevron(p)
        if p <= 0:
            self.sci_clip.grid_remove()
            return
        if not self.sci_clip.winfo_ismapped():
            self.sci_clip.grid()
        h = SCI_PANEL_H * p
        self.sci_clip.configure(height=max(1, round(h)))
        self.sci_frame.place(x=0, y=round(h - SCI_PANEL_H), relwidth=1)

    def _toggle_motion(self, save=True):
        """No flashing: no ripples (mouse or keyboard) and no coloured border flash. Smooth movement
        (panel swoop, sliding tabs, gliding switches, hover fades) stays: it replaces one-frame jumps."""
        RippleButton.enabled = not self.motion_sw.get()
        if save:
            self._schedule_save()

    def _set_angle(self, v):
        self.engine.deg = v == "DEG"
        self.on_change()
        self._schedule_save()

    # ================= calculator tab ====================================== #
    def _build_calc_tab(self):
        t = self.tabs.tab("Calculator")
        t.grid_columnconfigure(0, weight=1)

        self.entry = ctk.CTkEntry(t, height=50, justify="right", font=ctk.CTkFont(family=MONO, size=26))
        self.entry.grid(row=0, column=0, sticky="ew", padx=8, pady=(8, 2))
        self._entry_border = self.entry.cget("border_color")
        self.entry.bind("<Return>", self.calculate)
        self.entry.bind("<KP_Enter>", self.calculate)
        self.entry.bind("<Escape>", lambda e: (self._press_key("C"), self.clear()))
        self.entry.bind("<Up>", lambda e: self._hist_nav(-1))
        self.entry.bind("<Down>", lambda e: self._hist_nav(1))
        self.entry.bind("<KeyRelease>", self._on_key)
        self.entry.bind("<KeyPress>", self._ripple_for_key)

        ctk.CTkLabel(
            t, text_color=MUTED, anchor="e", font=ctk.CTkFont(size=12),
            text="Try:  5!  ·  2^10  ·  sin(30)  ·  x := 7  ·  f(x) := x^2+1  ·  "
                 "1+1=11 (validate!)  ·  ↑↓ history  ·  F1 = reference",
        ).grid(row=1, column=0, sticky="ew", padx=10)

        # Google-style display: the expression in small type above a big result
        self.expr_line = ctk.CTkLabel(t, text="", anchor="e", text_color=MUTED, height=24,
                                      font=ctk.CTkFont(family=MONO, size=17))
        self.expr_line.grid(row=2, column=0, sticky="ew", padx=12, pady=(6, 0))
        self._result_font = ctk.CTkFont(family=MONO, size=RESULT_FONT_MAX, weight="bold")
        # fixed height: when long results shrink the font, nothing below moves
        self.result = ctk.CTkLabel(t, text="0", anchor="e", text_color=TEXT, height=64, font=self._result_font)
        self.result.grid(row=3, column=0, sticky="ew", padx=12)
        self.result.bind("<Configure>", lambda e: self._fit_result())
        self.detail = ctk.CTkLabel(t, text="", anchor="e", text_color=MUTED, wraplength=700,
                                   font=ctk.CTkFont(family=MONO, size=13))
        self.detail.grid(row=4, column=0, sticky="ew", padx=12)

        bar = ctk.CTkFrame(t, fg_color="transparent")
        bar.grid(row=5, column=0, sticky="ew", padx=8, pady=(4, 2))
        self.mem_label = ctk.CTkLabel(bar, text="M: 0", text_color=MUTED)
        self.mem_label.pack(side="left", padx=4)
        self.var_label = ctk.CTkLabel(bar, text="", text_color=MUTED)
        self.var_label.pack(side="left", padx=12)
        RippleButton(bar, text="📋 Copy result", width=110, height=26, command=self._copy_result).pack(side="right")

        pad = ctk.CTkFrame(t, fg_color="transparent")
        pad.grid(row=6, column=0, sticky="nsew", padx=4, pady=4)
        pad.grid_columnconfigure(0, weight=1)
        t.grid_rowconfigure(6, weight=1)

        # memory row
        mem = ctk.CTkFrame(pad, fg_color="transparent")
        mem.grid(row=0, column=0, sticky="ew")
        self.sci_toggle = self._btn(mem, "fx", self.toggle_scientific, 0, 0, "mem", cls=ChevronButton)
        mem_buttons = [("MC", self.mem_clear), ("MR", self.mem_recall), ("M+", lambda: self.mem_add(1)),
                       ("M−", lambda: self.mem_add(-1)), ("ANS", lambda: self.insert("ans")),
                       ("≟ check", lambda: self.insert("="))]
        for c, (txt, cmd) in enumerate(mem_buttons, 1):
            self._btn(mem, txt, cmd, 0, c, "mem")

        # scientific block, inside a clip whose height is animated (see set_scientific)
        self._sci_open, self._sci_p, self._sci_job, self._sci_generation = True, 1.0, None, 0
        self.sci_clip = ctk.CTkFrame(pad, fg_color="transparent", corner_radius=0, height=SCI_PANEL_H)
        self.sci_clip.grid(row=1, column=0, sticky="ew")
        self.sci_frame = ctk.CTkFrame(self.sci_clip, fg_color="transparent", corner_radius=0)
        self.sci_frame.place(x=0, y=0, relwidth=1)
        sci = [
            [("sin", "sin("), ("cos", "cos("), ("tan", "tan("), ("asin", "asin("), ("acos", "acos("), ("atan", "atan(")],
            [("log", "log("), ("ln", "ln("), ("√", "sqrt("), ("∛", "cbrt("), ("x²", "^2"), ("xʸ", "^")],
            [("n!", "!"), ("π", "pi"), ("e", "e"), ("nCr", "ncr("), ("nPr", "npr("), ("|x|", "abs(")],
            [("mod", " mod "), ("gcd", "gcd("), ("lcm", "lcm("), ("1/x", None), ("±", None), (",", ",")],
        ]
        wrappers = {"1/x": ("1/(", ")"), "±": ("-(", ")")}
        for r, row in enumerate(sci):
            for c, (label, ins) in enumerate(row):
                if label in wrappers:
                    cmd = lambda w=wrappers[label]: self.wrap(*w)
                else:
                    cmd = lambda s=ins: self.insert(s)
                self._btn(self.sci_frame, label, cmd, r, c, "fn")

        # main keypad
        main = ctk.CTkFrame(pad, fg_color="transparent")
        main.grid(row=2, column=0, sticky="ew")
        keys = [
            [("C", "clr"), ("⌫", "clr"), ("(", "fn"), (")", "fn")],
            [("7", "num"), ("8", "num"), ("9", "num"), ("÷", "op")],
            [("4", "num"), ("5", "num"), ("6", "num"), ("×", "op")],
            [("1", "num"), ("2", "num"), ("3", "num"), ("−", "op")],
            [("0", "num"), (".", "num"), ("%", "fn"), ("+", "op")],
        ]
        special = {"C": self.clear, "⌫": self.backspace}
        for r, row in enumerate(keys):
            for c, (label, kind) in enumerate(row):
                cmd = special.get(label) or (lambda s=label: self.insert(s))
                self._btn(main, label, cmd, r, c, kind)
        self._btn(main, "=", self.calculate, len(keys), 0, "eq", span=4)
        self._fix_backspace_glyph()

    def _fix_backspace_glyph(self):
        """'⌫' is missing from many default fonts and renders as a broken box; use a font that has it."""
        installed = set(tk.font.families(self))
        family = next((f for f in BACKSPACE_FONTS if f in installed), None)
        key = self._keypad["⌫"]
        if family:
            key.configure(font=ctk.CTkFont(family=family, size=20, weight="bold"))
        else:
            key.configure(text="DEL")

    BUTTON_PALETTE = {
        "num": (("gray78", "gray30"), ("gray68", "gray38"), TEXT),
        "fn": (("gray70", "gray24"), ("gray60", "gray32"), TEXT),
        "mem": (("gray82", "gray20"), ("gray72", "gray28"), TEXT),
        "op": (("#3B8ED0", "#1F6AA5"), ("#2F78B3", "#27507A"), "white"),
        "eq": ((GREEN, "#106A43"), ("#25855D", "#0D5636"), "white"),
        "clr": ((RED, "#A33A36"), ("#C23A3F", "#872F2B"), "white"),
    }

    def _btn(self, parent, text, cmd, r, c, kind="num", span=1, cls=None):
        fg, hv, tc = self.BUTTON_PALETTE[kind]
        b = (cls or RippleButton)(parent, text=text, command=cmd, fg_color=fg, hover_color=hv, text_color=tc,
                                  height=KEY_HEIGHT, font=ctk.CTkFont(size=16, weight="bold"))
        b.grid(row=r, column=c, columnspan=span, sticky="nsew", padx=KEY_PAD, pady=KEY_PAD)
        for cc in range(c, c + span):
            parent.grid_columnconfigure(cc, weight=1, uniform="k")
        self._keypad.setdefault(text, b)
        return b

    def _press_key(self, label):
        """Ripple a keypad button, so typing on the keyboard gets the same feedback as clicking."""
        b = self._keypad.get(label)
        if b is not None:
            b.ripple()

    def _ripple_for_key(self, e):
        if e.char.isalpha() or e.state & 0x4:  # letters are names being typed; Ctrl+key is a shortcut
            return
        label = KEY_TO_BUTTON.get(e.char) or KEY_TO_BUTTON.get(e.keysym) or e.char
        self._press_key(label)

    # ---- entry helpers ----------------------------------------------------- #
    def _remember(self, kind):
        """Record an undo step for edits made by buttons (keyboard edits record themselves)."""
        editing = getattr(self.entry._entry, "_editing", None)
        if editing is not None:
            editing.snapshot(kind)

    def insert(self, text):
        self._remember("type")
        if not self.entry.get().strip() and text.strip() in ("+", "−", "×", "÷", "^", "%", "mod", "!", "^2"):
            self.entry.insert(0, "ans")
        self.entry.insert(self.entry.index("insert"), text)
        self.entry.focus_set()
        self.on_change()

    def wrap(self, pre, post):
        txt = self.entry.get().strip() or "ans"
        self._set_entry(f"{pre}{txt}{post}")

    def _set_entry(self, text):
        self._remember("replace")
        self.entry.delete(0, "end")
        self.entry.insert(0, text)
        self.entry.icursor("end")
        self.entry.focus_set()
        self.on_change()

    def backspace(self):
        self._remember("delete")
        pos = self.entry.index("insert")
        if pos > 0:
            self.entry.delete(pos - 1, pos)
        self.entry.focus_set()
        self.on_change()

    def clear(self):
        self._remember("replace")
        self.entry.delete(0, "end")
        self.hist_idx = None
        self.last_text = ""
        self.expr_line.configure(text="")
        self._show("0", TEXT, "")
        self.entry.focus_set()

    def _hist_nav(self, d):
        if not self.history:
            return "break"
        i = (len(self.history) if self.hist_idx is None else self.hist_idx) + d
        if i >= len(self.history):
            self.hist_idx = None
            self._set_entry("")
            return "break"
        self.hist_idx = max(0, i)
        self._set_entry(self.history[self.hist_idx]["expr"])
        return "break"

    # ---- memory ------------------------------------------------------------- #
    def _current_value(self):
        try:
            out = self.engine.process(self.entry.get(), commit=False)
            if isinstance(out, (ValueResult, Assignment)):
                return out.value
        except CalcError:
            pass
        return self.engine.ans

    def mem_add(self, sign):
        self.engine.memory = _guard_int(self.engine.memory + sign * self._current_value())
        self._refresh_mem()
        self._schedule_save()

    def mem_clear(self):
        self.engine.memory = 0
        self._refresh_mem()
        self._schedule_save()

    def mem_recall(self):
        text = fmt(self.engine.memory, 15)
        # insert the exact value when it fits, otherwise refer to the memory register itself
        self.insert(text if "e" not in text else "m")

    def _refresh_mem(self):
        self.mem_label.configure(text=f"M: {fmt(self.engine.memory)}")

    # ---- evaluating ---------------------------------------------------------- #
    def _show(self, text, color, detail=""):
        self.result.configure(text=text, text_color=color)
        self.detail.configure(text=detail)
        self._fit_result()

    def _fit_result(self):
        """Shrink the result font until the text fits (Google-style) instead of cutting it off."""
        avail = self.result.winfo_width() - 8
        if avail < 50:
            return
        scale = self.result._get_widget_scaling()
        text = self.result.cget("text")
        probe = tkinter.font.Font(family=MONO, weight="bold")
        size = RESULT_FONT_MAX
        while size > RESULT_FONT_MIN:
            probe.configure(size=-round(size * scale))  # CTk font sizes are pixels before scaling
            if probe.measure(text) <= avail:
                break
            size -= 2
        if size != self._result_font.cget("size"):
            self._result_font.configure(size=size)

    @staticmethod
    def _describe(out: Result, preview=False):
        """Return (text, color, detail) for an engine outcome."""
        dim = MUTED if preview else TEXT
        if isinstance(out, ValueResult):
            return group_digits(fmt(out.value)), dim, insights(out.value)
        if isinstance(out, Assignment):
            note = "will be stored as a variable" if preview else "variable stored"
            return f"{out.name} = {group_digits(fmt(out.value))}", dim, note
        if isinstance(out, FunctionDef):
            note = "will be stored as a function" if preview else "function stored · try it in the Graph tab"
            return f"{out.name}({', '.join(out.params)}) = {pretty_expr(out.body)}", dim, note
        chain = fmt(out.values[0]) + "".join(f" {op} {fmt(v)}" for op, v in zip(out.ops, out.values[1:]))
        if out.ok:
            return "✔ Correct", GREEN, f"Checked: {chain}"
        detail = f"Evaluated: {chain}"
        if len(out.ops) == 1 and out.ops[0] in ("=", "=="):
            detail += f"   ·   {out.exprs[0].strip()} is actually {fmt(out.values[0])}"
        return "✘ Wrong", RED, detail

    def on_change(self):
        raw = self.entry.get()
        # once you start typing again, the line above shows the previous answer (like Google's "Ans = 84")
        self.expr_line.configure(text=f"Ans = {group_digits(fmt(self.engine.ans))}" if self.history else "")
        if not raw.strip():
            self._show("0", TEXT, "")
            return
        text = raw + ")" * max(0, raw.count("(") - raw.count(")"))  # auto-close for preview
        try:
            out = self.engine.process(text, commit=False)
        except CalcError:
            self.detail.configure(text="")
            return
        except Exception:
            return
        self._show(*self._describe(out, preview=True))

    _NAV_KEYS = frozenset(("Return", "KP_Enter", "Up", "Down", "Left", "Right", "Escape", "Home", "End",
                           "Shift_L", "Shift_R", "Control_L", "Control_R", "Alt_L", "Alt_R"))

    def _on_key(self, e):
        if e.keysym in self._NAV_KEYS:
            return
        self.hist_idx = None
        self.on_change()

    def calculate(self, event=None):
        if event is not None:  # Enter key: give the "=" button the same feedback as a click
            self._press_key("=")
        raw = self.entry.get().strip()
        if not raw:
            return "break"
        self.hist_idx = None
        self.expr_line.configure(text=pretty_expr(raw))
        try:
            out = self.engine.process(raw)
            text, color, detail = self._describe(out)
        except CalcError as ex:
            self._show("Error", RED, str(ex))
            self._flash(RED)
            return "break"
        except Exception as ex:  # never crash the UI
            self._show("Error", RED, f"Unexpected problem: {ex}")
            self._flash(RED)
            return "break"

        self._show(text, color, detail)
        # display text has thousands separators; copies and history get the plain, re-typeable form
        if isinstance(out, ValueResult):
            self.expr_line.configure(text=pretty_expr(raw) + " =")
            plain = self.last_text = fmt(out.value)
        elif isinstance(out, Assignment):
            plain = f"{out.name} = {fmt(out.value)}"
            self.last_text = fmt(out.value)
        else:
            plain = self.last_text = text
            if isinstance(out, Check):
                self._flash(GREEN if out.ok else RED)
        self._add_history(raw, plain)
        self._refresh_vars()
        return "break"

    def _flash(self, color):
        """Briefly colour the entry border (skipped with Reduce motion)."""
        if self.motion_sw.get():
            return
        self.entry.configure(border_color=color)
        self.after(900, lambda: self.entry.configure(border_color=self._entry_border))

    def _refresh_vars(self):
        parts = [f"{k}={fmt(v)}" for k, v in list(self.engine.vars.items())[:5]]
        parts += [f.signature for f in list(self.engine.user_funcs.values())[:4]]
        self.var_label.configure(text="defined: " + ", ".join(parts) if parts else "")

    def _copy_result(self):
        self._copy(self.last_text or self.result.cget("text"))

    def _copy(self, text):
        self.clipboard_clear()
        self.clipboard_append(text)
        self.detail.configure(text=f"Copied: {text}")

    # ================= history sidebar ===================================== #
    def _build_sidebar(self):
        side = ctk.CTkFrame(self, width=300, corner_radius=12)
        side.grid(row=1, column=1, sticky="nsew", padx=(0, 10), pady=(8, 10))
        side.pack_propagate(False)
        ctk.CTkLabel(side, text="🕘 History", font=ctk.CTkFont(size=16, weight="bold")).pack(anchor="w", padx=14, pady=(12, 4))
        ctk.CTkLabel(side, text="click = reuse · right-click = copy result", text_color=MUTED,
                     font=ctk.CTkFont(size=11)).pack(anchor="w", padx=14)
        self.hist_frame = ctk.CTkScrollableFrame(side, fg_color="transparent")
        self.hist_frame.pack(fill="both", expand=True, padx=4, pady=6)
        row = ctk.CTkFrame(side, fg_color="transparent")
        row.pack(fill="x", padx=10, pady=(0, 10))
        RippleButton(row, text="Clear", width=70, fg_color=(RED, "#A33A36"), hover_color=("#C23A3F", "#872F2B"),
                      command=self._clear_history).pack(side="left", padx=2)
        RippleButton(row, text="Export .txt", command=self._export_history).pack(side="right", padx=2, fill="x", expand=True)

    def _add_history(self, expr, result):
        item = {"expr": expr, "result": result, "t": datetime.now().strftime("%Y-%m-%d %H:%M:%S")}
        self.history.append(item)
        del self.history[:-HISTORY_LIMIT]
        self._prepend_history_widget(item)
        self._schedule_save()

    def _make_history_widget(self, item):
        e = item["expr"] if len(item["expr"]) <= 30 else item["expr"][:28] + "…"
        b = RippleButton(self.hist_frame, text=f"{e}\n= {item['result']}", anchor="w", height=46,
                          fg_color="transparent", hover_color=("gray85", "gray25"), text_color=TEXT,
                          command=lambda x=item["expr"]: self._set_entry(x))
        for seq in ("<Button-2>", "<Button-3>"):
            b.bind(seq, lambda ev, r=item["result"]: self._copy(r))
        return b

    def _prepend_history_widget(self, item):
        """Add one entry on top instead of rebuilding the whole list."""
        b = self._make_history_widget(item)
        if self._hist_widgets:
            b.pack(fill="x", pady=1, before=self._hist_widgets[0])
        else:
            b.pack(fill="x", pady=1)
        self._hist_widgets.insert(0, b)
        while len(self._hist_widgets) > HISTORY_SHOWN:
            self._hist_widgets.pop().destroy()

    def _render_history(self):
        for w in self._hist_widgets:
            w.destroy()
        self._hist_widgets = []
        for item in reversed(self.history[-HISTORY_SHOWN:]):
            b = self._make_history_widget(item)
            b.pack(fill="x", pady=1)
            self._hist_widgets.append(b)

    def _clear_history(self):
        self.history = []
        self._render_history()
        self._schedule_save()

    def _export_history(self):
        if not self.history or self._dialog_open:
            return
        self._dialog_open = True
        ask_save_path(self, "Export history", "ultracalc_history.txt", [("Text file", "txt")],
                      self._write_history_export, folder=self._last_save_dir)

    def _write_history_export(self, path):
        self._dialog_open = False
        if not path:
            return
        self._last_save_dir = os.path.dirname(path)
        try:
            with open(path, "w", encoding="utf-8") as f:
                f.writelines(f"[{i.get('t', '')}]  {i['expr']}  =>  {i['result']}\n" for i in self.history)
            self.detail.configure(text=f"History exported to {path}")
        except OSError as ex:
            self.detail.configure(text=f"Export failed: {ex}")

    def _load_history(self):
        try:
            with open(HISTORY_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
            if isinstance(data, list):
                self.history = [d for d in data if isinstance(d, dict) and "expr" in d and "result" in d][-HISTORY_LIMIT:]
        except (OSError, ValueError):
            self.history = []
        self._render_history()

    def _schedule_save(self):
        """Persist history and settings shortly after changes so a crash doesn't lose them."""
        if self._save_job:
            self.after_cancel(self._save_job)
        self._save_job = self.after(1500, self._save_state)

    def _save_state(self):
        self._save_job = None
        _write_json_atomic(HISTORY_FILE, self.history[-HISTORY_LIMIT:])
        _write_json_atomic(SETTINGS_FILE, self._settings_snapshot())

    def _on_close(self):
        if self._save_job:
            self.after_cancel(self._save_job)
        self._save_state()
        self.destroy()

    # ================= graph tab ============================================ #
    def _build_graph_tab(self):
        t = self.tabs.tab("Graph")
        top = ctk.CTkFrame(t, fg_color="transparent")
        top.pack(fill="x", padx=6, pady=6)
        self.g_mode_bar = GlideSegments(top, list(GRAPH_MODES), command=self._set_graph_mode)
        self.g_mode_bar.pack(side="left", padx=(2, 6))
        self.g_label = ctk.CTkLabel(top, text="")
        self.g_label.pack(side="left", padx=(4, 2))
        self.g_f = ctk.CTkEntry(top)
        self.g_f.pack(side="left", padx=4, fill="x", expand=True)
        self.g_f.bind("<Return>", lambda e: self.plot())
        RippleButton(top, text="Save…", width=70, command=self.export_graph).pack(side="left", padx=(4, 2))
        # second row: range fields (relabelled per mode), Plot and Presets
        row2 = ctk.CTkFrame(t, fg_color="transparent")
        row2.pack(fill="x", padx=6)
        self.g_vals, self.g_fields = {}, {}
        for key in RANGE_KEYS:
            box = ctk.CTkFrame(row2, fg_color="transparent")
            label = ctk.CTkLabel(box, text=key)
            label.pack(side="left", padx=(8, 2))
            en = ctk.CTkEntry(box, width=64, placeholder_text="auto" if key[0] == "y" else "")
            en.pack(side="left")
            en.bind("<Return>", lambda e: self.plot())
            self.g_vals[key], self.g_fields[key] = en, (box, label)
        self.g_plot_btn = RippleButton(row2, text="Plot", width=70, command=self.plot)
        self.g_plot_btn.pack(side="left", padx=8)
        self.g_preset_menu = GlideOptionMenu(row2, values=["Presets"], width=130, command=self._preset)
        self.g_preset_menu.pack(side="left")
        # log scales (y = f(x) mode only; shown/hidden by _set_graph_mode)
        self.g_logx = GlideSwitch(row2, text="log x", width=64, switch_width=32, command=self._toggle_log)
        self.g_logy = GlideSwitch(row2, text="log y", width=64, switch_width=32, command=self._toggle_log)
        # Implicit mode: join all parts into one solid (modelling) instead of separate surfaces (maths)
        self.g_join = GlideSwitch(row2, text="join parts", width=96, switch_width=32, command=self.plot)
        self.g_info = ctk.CTkLabel(t, text="", text_color=MUTED, anchor="w")
        self.g_info.pack(fill="x", padx=12)
        # the plot itself is Matplotlib, created the first time the Graph tab is shown
        self.g_host = ctk.CTkFrame(t, fg_color="transparent", corner_radius=0)
        self.g_host.pack(fill="both", expand=True, padx=8, pady=8)
        self._mpl = None
        self._mesh = None        # (vertices, faces) of the 3D shape on screen, for STL export
        self._gl = None          # GPU 3D view, created on first use (False if OpenGL isn't available)
        self._graph_kind = None  # which widget is showing: "mpl" or "gl"
        self._g_mode = None
        self._g_saved = {mode: {"expr": spec["expr"], "range": list(spec["defaults"])} for mode, spec in GRAPH_MODES.items()}
        self._set_graph_mode(next(iter(GRAPH_MODES)), replot=False)

    def _set_entry_text(self, en, value):
        en.delete(0, "end")
        if value:
            en.insert(0, value)
        elif self.focus_get() is not en._entry:
            en._activate_placeholder()  # show "auto" again

    def _set_graph_mode(self, mode, replot=True):
        """Switch between y = f(x), polar, parametric and 3D; each mode keeps its own inputs."""
        if self._g_mode is not None:
            self._g_saved[self._g_mode] = {"expr": self.g_f.get(), "range": [self.g_vals[k].get() for k in RANGE_KEYS]}
            # switching between the OpenGL and Matplotlib views swaps the whole picture: dissolve it instead.
            # Build the GPU view first (invisible until shown) so the blend's hold only covers the first frame.
            gpu_next = "mesh" in GRAPH_MODES[mode] and self.tabs.get() == "Graph" and bool(self._ensure_gl())
            if (replot and self._graph_kind and (self._graph_kind == "gl") != gpu_next
                    and self.tabs.get() == "Graph" and kwin_blend_available()):
                kwin_blend(300)
        self._g_mode, self._drag = mode, None
        spec, saved = GRAPH_MODES[mode], self._g_saved[mode]
        if self.g_mode_bar.get() != mode:
            self.g_mode_bar.set(mode, animate=False)
        self.g_label.configure(text=spec["label"])
        self._set_entry_text(self.g_f, saved["expr"])
        for i, key in enumerate(RANGE_KEYS):
            box, label = self.g_fields[key]
            box.pack_forget()
            if i < len(spec["fields"]):
                label.configure(text=spec["fields"][i])
                box.pack(side="left", before=self.g_plot_btn)
            self._set_entry_text(self.g_vals[key], saved["range"][i])
        self.g_preset_menu.configure(values=["Presets", *spec["presets"]])
        self.g_preset_menu.set("Presets")
        for switch in (self.g_logx, self.g_logy):
            switch.pack_forget()
            if spec["draw"] == "_draw_function":
                switch.pack(side="left", padx=(10, 0))
        self.g_join.pack_forget()
        if spec.get("mesh") == "_mesh_implicit":
            self.g_join.pack(side="left", padx=(10, 0))
        self.g_info.configure(text=spec["info"], text_color=MUTED)
        if replot:
            self.plot()

    # ---- graph view: zoom / pan / reset (y = f(x) mode)
    def _set_view(self, xmin, xmax, ymin=None, ymax=None):
        for key, v in zip(RANGE_KEYS, (xmin, xmax, ymin, ymax)):
            self._set_entry_text(self.g_vals[key], None if v is None else f"{v:.10g}")
        self._schedule_plot(0)  # coalesces bursts of wheel/drag events into one redraw per idle

    def _reset_view(self):
        self._drag = None
        if self.g_logx.get():
            self._set_view(0.01, 100)
        else:
            self._set_view(-10, 10)

    def _toggle_log(self):
        self._drag = None
        if self.g_logx.get() and (self._graph_number_or_none("xmin") or 0) <= 0:
            self._set_view(0.01, 100)  # a log axis can't start at zero or below: pick a useful range
        else:
            self.plot()

    def _graph_number_or_none(self, key):
        try:
            return self._graph_number(key)
        except CalcError:
            return None

    @staticmethod
    def _scale_fns(log):
        """(to-screen-space, back) for an axis: log10 for log axes, identity otherwise."""
        return (math.log10, lambda u: 10 ** u) if log else ((lambda v: v), (lambda u: u))

    def export_graph(self):
        """Save the current graph: PNG/SVG/PDF from Matplotlib, PNG from the GPU 3D view."""
        if self.tabs.get() != "Graph" or not (self._mpl or self._gl) or self._dialog_open:
            return
        gpu = self._graph_kind == "gl"
        filters = ([("PNG image (3D is drawn on the GPU, so it saves as pixels)", "png")] if gpu else
                   [("PNG image", "png"), ("SVG vector image", "svg"), ("PDF document", "pdf")])
        if self._mesh is not None:  # a 3D shape: offer it as a 3D model first
            filters.insert(0, ("STL 3D model (Blender, 3D printing, CAD)", "stl"))
        self._dialog_open = True
        ask_save_path(self, "Save graph", f"{'model' if self._mesh is not None else 'graph'}.{filters[0][1]}", filters,
                      lambda path: self._save_graph(path, gpu), folder=self._last_save_dir)

    def _save_graph(self, path, gpu):
        self._dialog_open = False
        if not path:
            return
        self._last_save_dir = os.path.dirname(path)
        try:
            if path.lower().endswith(".stl") and self._mesh is not None:
                vertices, faces = merge_parts(self._mesh)  # every surface into one STL
                write_stl(path, vertices, faces)
                self.g_info.configure(text=f"Saved 3D model ({len(faces):,} triangles) to {path}",
                                      text_color=MUTED)
                return
            if gpu:
                import matplotlib.image
                if not path.lower().endswith(".png"):
                    path += ".png"
                matplotlib.image.imsave(path, self._gl.canvas.render())
            else:
                m = self._mpl
                m.fig.savefig(path, dpi=200, facecolor=m.fig.get_facecolor())  # format from the extension
                m.canvas.draw_idle()  # refresh the on-screen image and the trace's cached background
            self.g_info.configure(text=f"Saved {path}", text_color=MUTED)
        except Exception as ex:
            self.g_info.configure(text=f"⚠ Couldn't save: {ex}", text_color=RED)

    def _preset(self, name):
        preset = GRAPH_MODES[self._g_mode]["presets"].get(name)
        self.g_preset_menu.set("Presets")
        if not preset:
            return
        expr, ranges = preset
        self._set_entry_text(self.g_f, expr)
        for key, value in zip(RANGE_KEYS, ranges or ()):
            self._set_entry_text(self.g_vals[key], value)
        self.plot()

    def _schedule_plot(self, delay=60):
        if self._plot_job:
            self.after_cancel(self._plot_job)
        self._plot_job = self.after(delay, self.plot)

    def _graph_number(self, key, default=None):
        text = self.g_vals[key].get().strip() or default
        return None if text is None else float(self.engine.evaluate(text))

    def _graph_range(self, lo_key, hi_key, lo_default, hi_default, name):
        lo, hi = self._graph_number(lo_key, lo_default), self._graph_number(hi_key, hi_default)
        if hi <= lo:
            raise CalcError(f"The end of the {name} range must be bigger than its start")
        return lo, hi

    def _ensure_mpl(self):
        """Create the Matplotlib figure on first use; None if Matplotlib isn't installed."""
        if self._mpl is not None:
            return self._mpl or None
        try:
            from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
            from matplotlib.figure import Figure
        except ImportError:
            self._mpl = False
            ctk.CTkLabel(self.g_host, text="The graph needs Matplotlib:   pip install matplotlib",
                         text_color=MUTED).pack(expand=True)
            return None

        class SmoothCanvas(FigureCanvasTkAgg):
            def _resize_figure_for_canvas_size(self, width, height):
                super()._resize_figure_for_canvas_size(width, height)
                if width > 0 and height > 0:
                    self.draw()  # render now: the backend clears its image and would show it blank for a frame

        fig = Figure(dpi=100)
        canvas = SmoothCanvas(fig, master=self.g_host)
        widget = canvas.get_tk_widget()
        widget.configure(highlightthickness=0, bd=0, cursor="crosshair")
        widget.pack(fill="both", expand=True)
        self._mpl = m = type("Mpl", (), {})()
        m.fig, m.canvas, m.widget, m.bg, m.ax, m.projection = fig, canvas, widget, None, None, "unset"
        for event, handler in (("draw_event", self._mpl_cache_background), ("motion_notify_event", self._mpl_motion),
                               ("figure_leave_event", lambda e: self._mpl_hide_trace()),
                               ("scroll_event", self._mpl_scroll), ("button_press_event", self._mpl_press),
                               ("button_release_event", self._mpl_release)):
            canvas.mpl_connect(event, handler)
        return m

    def _mpl_axes(self, projection):
        """Axes for the current mode: recreated when the projection changes (polar/3D), else cleared."""
        m = self._mpl
        if m.projection != projection:
            m.fig.clear()
            m.ax, m.projection = m.fig.add_subplot(projection=projection), projection
            margins = (dict(left=0, right=1, top=1, bottom=0) if projection == "3d"
                       else dict(left=0.055, right=0.975, top=0.985, bottom=0.065))
            m.fig.subplots_adjust(**margins)
        else:
            m.ax.cla()
        for artist in [*m.fig.texts, *m.fig.legends]:
            artist.remove()
        return m.ax

    # ---- GPU 3D view (VisPy / OpenGL); Matplotlib's CPU 3D is the fallback
    def _ensure_gl(self):
        """Create the OpenGL 3D view on first use; None if VisPy/OpenGL aren't usable here."""
        if self._gl is not None:
            return self._gl or None
        try:
            if sys.platform.startswith("linux"):
                os.environ.setdefault("PYOPENGL_PLATFORM", "glx")  # Tk is X11; under Wayland PyOpenGL would pick EGL
            import numpy as np
            try:  # pyopengltk prints GLX debug info ("GLX version: 1.4", ...) on every context; keep the terminal clean
                import pyopengltk.linux
                pyopengltk.linux.print = lambda *args, **kwargs: None
            except ImportError:
                pass
            from vispy import scene
            from vispy.color import get_colormap
            canvas = scene.SceneCanvas(app="tkinter", parent=self.g_host, keys=None)
        except Exception:
            self._gl = False
            return None
        native = canvas.native

        def map_or_fall_back(event, create=native.tkMap):
            # the OpenGL context is only made when the view first appears; if that fails (e.g. the system's
            # GPU driver won't load) the canvas would show leftover video memory, so use Matplotlib instead
            try:
                create(event)
            except Exception:
                for sequence in ("<Map>", "<Configure>", "<Expose>"):
                    native.unbind(sequence)
                self.after_idle(self._gl_unavailable)
        native.bind("<Map>", map_or_fall_back)
        g = self._gl = type("Gl", (), {})()
        g.canvas, g.colormap = canvas, get_colormap("viridis")
        _restore_depth_writes(canvas)
        g.view = canvas.central_widget.add_view()
        g.view.camera = scene.TurntableCamera(fov=40, elevation=28, azimuth=-55, distance=2.4)
        # near/far = distance ÷/× 10. VisPy's default (÷/× 1000) wastes depth precision on a unit-sized scene,
        # which made crossing surfaces z-fight into sawtooth edges
        g.view.camera.depth_value = 100
        # every 3D mode (height map, (u,v) surface, implicit shape) is drawn as one triangle mesh
        g.scene, g.meshes = scene, []  # one mesh visual per surface, created on demand (_gl_show_mesh)
        g.box = scene.visuals.Line(pos=np.zeros((2, 3)), connect="segments", width=1, parent=g.view.scene)
        # title and the x/y/z ranges sit in the corner, in screen space: captions placed in 3D next to the
        # box ended up drawn across the shape from most viewing angles
        g.title = scene.visuals.Text("", font_size=11, bold=True, anchor_x="left", anchor_y="center", pos=(14, 20),
                                     parent=canvas.scene, color=GRAPH_COLORS[0])
        g.caption = scene.visuals.Text("", font_size=9, anchor_x="left", anchor_y="center", pos=(14, 42),
                                       parent=canvas.scene)
        for text in (g.title, g.caption):  # drawn last each frame: leave depth writes on (see _restore_depth_writes)
            text.set_gl_state("translucent", depth_test=False, depth_mask=True)
        return g

    def _gl_unavailable(self):
        """The OpenGL view got no working context: drop it for good and redraw with Matplotlib."""
        g, self._gl = self._gl, False
        if g:
            g.canvas.native.is_destroyed = True  # VisPy then skips its already-scheduled redraws
            g.canvas.native.pack_forget()
        if self._graph_kind == "gl":
            self._graph_kind = None
            self._schedule_plot(0)

    def _show_graph_widget(self, kind):
        """Show either the Matplotlib widget or the OpenGL one in the graph area."""
        if self._graph_kind == kind:
            return
        widgets = {"mpl": self._mpl and self._mpl.widget, "gl": self._gl and self._gl.canvas.native}
        for other, w in widgets.items():
            if other != kind and w:
                w.pack_forget()
        widgets[kind].pack(fill="both", expand=True)
        self._graph_kind = kind

    def _gl_show_mesh(self, c, parts, title, flat_z=False, color_range=None):
        """Draw the parts fitted into the view (one shared fit), with a box, axis ranges and a title.
        ``flat_z`` (height maps) squashes z to half the width so landscapes read as landscapes; otherwise
        shapes keep their true proportions. Opaque surfaces are drawn first; see-through ones after,
        without hiding what lies behind them."""
        import numpy as np
        g = self._gl
        lo = np.min([p.vertices.min(axis=0) for p in parts], axis=0)
        hi = np.max([p.vertices.max(axis=0) for p in parts], axis=0)
        extent = np.maximum(hi - lo, 1e-12)
        scale = (np.array([1 / extent[0], 1 / extent[1], 0.5 / extent[2]]) if flat_z
                 else np.full(3, 1 / extent.max()))
        z0, z1 = color_range or (lo[2], hi[2])
        while len(g.meshes) < len(parts):  # one mesh visual per surface, created as needed
            mesh = g.scene.visuals.Mesh(vertices=np.zeros((3, 3), np.float32), faces=np.array([[0, 1, 2]], np.uint32),
                                        shading="smooth", parent=g.view.scene)
            mesh.shading_filter.ambient_light = (1, 1, 1, 0.55)  # keep colours readable on the shaded side
            g.meshes.append(mesh)
        old_order = [m.order for m in g.meshes]
        for mesh, part in zip(g.meshes, parts):
            if part.vertex_colors is not None:
                colors = part.vertex_colors
            elif part.rgba is not None:
                colors = np.tile(np.array(part.rgba, np.float32), (len(part.vertices), 1))
            else:  # a lone plain surface: colour by height
                colors = g.colormap.map(np.clip((part.vertices[:, 2] - z0) / max(z1 - z0, 1e-12), 0, 1))
                colors[:, 3] = part.alpha
            see_through = float(np.min(colors[:, 3])) < 1
            mesh.set_data(vertices=((part.vertices - (lo + hi) / 2) * scale).astype(np.float32), faces=part.faces,
                          vertex_colors=np.asarray(colors, np.float32))
            mesh.set_gl_state("translucent", depth_test=True, cull_face=False, depth_mask=not see_through)
            mesh.order = 1 if see_through else 0
            mesh.visible = True
        for mesh in g.meshes[len(parts):]:
            mesh.visible = False
        if [m.order for m in g.meshes] != old_order:
            g.canvas._update_scenegraph(None)  # VisPy caches its draw order and ignores later .order changes
        hx, hy, hz = extent * scale / 2
        corners = np.array([[x, y, z] for x in (-hx, hx) for y in (-hy, hy) for z in (-hz, hz)])
        edges = [(i, j) for i in range(8) for j in range(i + 1, 8) if bin(i ^ j).count("1") == 1]
        g.box.set_data(pos=np.array([corners[k] for e in edges for k in e]), color=c["grid"])
        g.caption.text = "      ".join(f"{axis}  {a:.3g} … {b:.3g}" for axis, a, b in zip("xyz", lo, hi))
        g.caption.color = c["txt"]
        g.title.text = title
        g.canvas.bgcolor = c["bg"]
        g.canvas.update()

    # ---- building the current 3D shape from the inputs (shared by the GPU view, the CPU fallback and STL export)
    @staticmethod
    def _parts_title(src, single):
        styled = styled_parts(src)
        if len(styled) == 1:
            return single(styled[0][0])
        return f"{len(styled)} surfaces: " + ",  ".join(style or f"#{i + 1}" for i, (_, style) in enumerate(styled))

    def _mesh_heightmap(self, coarse=False):
        x0, x1 = self._graph_range("xmin", "xmax", "-8", "8", "x")
        y0, y1 = self._graph_range("ymin", "ymax", repr(x0), repr(x1), "y")
        src = self.g_f.get().strip()
        parts, zrange = heightmap_parts(self.engine, src, x0, x1, y0, y1, n=70 if coarse else 150)
        return parts, self._parts_title(src, lambda e: "z = " + re.sub(r"^\s*z\s*=\s*", "", e)), zrange

    def _mesh_param_surface(self, coarse=False):
        u0, u1 = self._graph_range("xmin", "xmax", "0", "2*pi", "u")
        v0, v1 = self._graph_range("ymin", "ymax", "0", "2*pi", "v")
        src = self.g_f.get().strip()
        parts = surface_parts(self.engine, src, u0, u1, v0, v1, n=80 if coarse else 160)
        return parts, self._parts_title(src, lambda e: f"(x, y, z) = ({e})"), None

    def _mesh_implicit(self, coarse=False):
        lo, hi = self._graph_range("xmin", "xmax", "-2", "2", "box")
        detail = int(min(48 if coarse else 128, max(16, self._graph_number("ymin", "72"))))
        src = self.g_f.get().strip()  # not _expressions(): its "y = …" stripping would eat the equation
        parts = implicit_parts(self.engine, src, lo, hi, detail, join=bool(self.g_join.get()))
        return parts, self._parts_title(src, lambda e: e + ("" if "=" in e else " = 0")), None

    def _draw_3d_gl(self, c):
        parts, title, zrange = getattr(self, GRAPH_MODES[self._g_mode]["mesh"])()
        self._mesh = parts
        self._gl_show_mesh(c, parts, title, flat_z=self._g_mode == "3D", color_range=zrange)

    def _draw_3d_mpl(self, ax, c):
        """CPU fallback for the 3D modes when OpenGL isn't available."""
        import numpy as np
        from matplotlib.colors import to_rgba
        # Matplotlib draws triangles one by one in Python: build coarser meshes to stay responsive
        parts, title, zrange = getattr(self, GRAPH_MODES[self._g_mode]["mesh"])(coarse=True)
        self._mesh = parts
        everything = np.concatenate([p.vertices for p in parts])
        lo, hi = zrange or (float(everything[:, 2].min()), float(everything[:, 2].max()))
        for part in parts:
            v, f = part.vertices, part.faces
            surface = ax.plot_trisurf(v[:, 0], v[:, 1], v[:, 2], triangles=f, cmap="viridis", vmin=lo, vmax=hi,
                                      linewidth=0, antialiased=True, alpha=part.alpha)
            if part.vertex_colors is not None or part.rgba is not None:
                surface.set_array(None)  # solid or per-part colours instead of the height colour map
                surface.set_facecolor(part.vertex_colors[f[:, 0]] if part.vertex_colors is not None else part.rgba)
        if self._g_mode != "3D":
            ax.set_box_aspect(tuple(everything.max(axis=0) - everything.min(axis=0)))  # true proportions
        for axis, name in ((ax.xaxis, "x"), (ax.yaxis, "y"), (ax.zaxis, "z")):
            axis.set_pane_color(to_rgba(c["pane"]))
            axis._axinfo["grid"]["color"] = to_rgba(c["grid"])
            axis.label.set_color(c["txt"])
        ax.set_xlabel("x")
        ax.set_ylabel("y")
        ax.set_zlabel("z")
        ax.tick_params(colors=c["txt"], labelsize=8)
        self._mpl.fig.text(0.02, 0.97, title, color=GRAPH_COLORS[0], family="monospace",
                           fontsize=10, fontweight="bold", va="top")

    def plot(self):
        self._plot_job = None
        if self._mpl is None and self.tabs.get() != "Graph":
            return  # don't load Matplotlib until the graph is actually looked at
        m = self._ensure_mpl()
        if m is None:
            return
        dark = ctk.get_appearance_mode() == "Dark"
        colors = (dict(bg="#1c1c1c", grid="#2d2d2d", axis="#9a9a9a", txt="#aaaaaa", pane="#232323") if dark else
                  dict(bg="#ffffff", grid="#e6e6e6", axis="#555555", txt="#555555", pane="#f4f4f4"))
        spec = GRAPH_MODES[self._g_mode]
        self._mesh = None  # the current 3D shape, kept for STL export
        if "mesh" in spec and self._ensure_gl():
            self._show_graph_widget("gl")
            self._pl = None
            try:
                self._draw_3d_gl(colors)
                self.g_info.configure(text=spec["info"], text_color=MUTED)
            except (CalcError, RecursionError) as ex:
                msg = str(ex) if isinstance(ex, CalcError) else "Expression too deeply nested"
                self.g_info.configure(text=f"⚠ {msg}", text_color=RED)
            return
        self._show_graph_widget("mpl")
        ax = self._mpl_axes(spec["projection"])
        m.fig.set_facecolor(colors["bg"])
        ax.set_facecolor(colors["bg"])
        m.widget.configure(bg=colors["bg"])  # anything not yet drawn shows the plot colour, never a flash of grey
        self._pl = None
        try:
            getattr(self, spec["draw"])(ax, colors)
        except CalcError as ex:
            ax.set_axis_off()
            m.fig.text(0.5, 0.5, f"⚠ {ex}", ha="center", va="center", color=RED, fontsize=13)
        m.canvas.draw_idle()

    def _eval_on(self, fn, names, values):
        """Evaluate a compiled expression at each value (bound to every name in ``names``); None where undefined."""
        out, scope = [], {}
        with self.engine.angle_mode(False):  # graphs always use radians
            for v in values:
                for name in names:
                    scope[name] = v
                try:
                    out.append(float(fn.eval(scope)))
                except (CalcError, OverflowError):
                    out.append(None)
        return out

    def _style_cartesian(self, ax, c):
        ax.grid(True, color=c["grid"], linewidth=0.8)
        ax.tick_params(colors=c["txt"], labelsize=8, length=0)
        for spine in ax.spines.values():
            spine.set_visible(False)

    def _legend(self, ax, **kwargs):
        if ax.get_legend_handles_labels()[0]:
            ax.legend(frameon=False, labelcolor="linecolor", prop={"family": "monospace", "size": 9, "weight": "bold"},
                      **({"loc": "upper left"} | kwargs))

    def _expressions(self):
        srcs = [strip_lhs(s).strip() for s in self.g_f.get().split(";") if s.strip()][:MAX_GRAPHS]
        if not srcs:
            raise CalcError("Type something to plot")
        return srcs

    # ---- the four kinds of plot
    def _draw_function(self, ax, c):
        logx, logy = bool(self.g_logx.get()), bool(self.g_logy.get())
        xmin, xmax = self._graph_range("xmin", "xmax", "-10", "10", "x")
        if logx and xmin <= 0:
            raise CalcError("log x needs xmin > 0  (e.g. 0.01 to 100)")
        srcs = self._expressions()
        funcs = [self.engine.compile(s, params=("x",)) for s in srcs]
        n = 900
        to_u, from_u = self._scale_fns(logx)
        u0, u1 = to_u(xmin), to_u(xmax)
        xs = [from_u(u0 + (u1 - u0) * i / (n - 1)) for i in range(n)]  # even spacing on screen, also for log x
        series = [self._eval_on(fn, ("x",), xs) for fn in funcs]
        if logy:  # values <= 0 have no place on a log scale
            series = [[y if y is not None and y > 0 else None for y in ys] for ys in series]
        ymin, ymax = self._y_range(series, logy)
        if logy and ymin <= 0:
            raise CalcError("log y needs ymin > 0")
        if not (math.isfinite(ymax - ymin) and math.isfinite(xmax - xmin)):
            raise CalcError("Values are too large to plot")
        ax.set_xscale("log" if logx else "linear")
        ax.set_yscale("log" if logy else "linear")
        ax.set_xlim(xmin, xmax)
        ax.set_ylim(ymin, ymax)
        self._style_cartesian(ax, c)
        if not logy and ymin < 0 < ymax:
            ax.axhline(0, color=c["axis"], linewidth=1.2)
        if not logx and xmin < 0 < xmax:
            ax.axvline(0, color=c["axis"], linewidth=1.2)
        to_v = self._scale_fns(logy)[0]
        jump = (to_v(ymax) - to_v(ymin)) * 3  # bigger on-screen jumps between samples are discontinuities: break
        for color, src, ys in zip(GRAPH_COLORS, srcs, series):
            px, py, prev = [], [], None
            for x, y in zip(xs, ys):
                if y is not None and prev is not None and abs(to_v(y) - to_v(prev)) > jump:
                    px.append(x)
                    py.append(math.nan)
                px.append(x)
                py.append(math.nan if y is None else y)
                prev = y
            ax.plot(px, py, color=color, linewidth=2, label=src, solid_capstyle="round")
        self._legend(ax)
        # hover-trace artists: animated, so they're blitted on top instead of redrawing the whole plot
        m = self._mpl
        m.vline = ax.axvline(xmin, color="#888888", linestyle=(0, (3, 3)), linewidth=1, animated=True)
        m.dot, = ax.plot([], [], "o", color="#FFD43B", markersize=7, animated=True)
        m.label = ax.text(0.99, 0.985, "", transform=ax.transAxes, ha="right", va="top", color="#FFD43B",
                          family="monospace", fontsize=11, fontweight="bold", animated=True)
        self._pl = dict(xmin=xmin, xmax=xmax, ymin=ymin, ymax=ymax, funcs=funcs, logx=logx, logy=logy)

    def _draw_polar(self, ax, c):
        t0, t1 = self._graph_range("xmin", "xmax", "0", "2*pi", "θ")
        srcs = self._expressions()
        funcs = [self.engine.compile(s, params=("theta", "t")) for s in srcs]
        ts = [t0 + (t1 - t0) * i / 1499 for i in range(1500)]
        ax.grid(True, color=c["grid"], linewidth=0.8)
        ax.tick_params(colors=c["txt"], labelsize=8)
        ax.spines["polar"].set_color(c["grid"])
        for color, src, fn in zip(GRAPH_COLORS, srcs, funcs):
            th, r = [], []
            for t, v in zip(ts, self._eval_on(fn, ("theta", "t"), ts)):
                if v is None:
                    th.append(t)
                    r.append(math.nan)
                else:  # a negative radius points the other way
                    th.append(t if v >= 0 else t + math.pi)
                    r.append(abs(v))
            ax.plot(th, r, color=color, linewidth=2, label=src)
        # anchored to the figure's corner: relative to the round axes it ran off-screen on wide windows
        self._legend(ax, loc="upper left", bbox_to_anchor=(0.01, 0.99), bbox_transform=self._mpl.fig.transFigure)

    def _draw_parametric(self, ax, c):
        t0, t1 = self._graph_range("xmin", "xmax", "0", "2*pi", "t")
        ts = [t0 + (t1 - t0) * i / 1999 for i in range(2000)]
        self._style_cartesian(ax, c)
        for color, src in zip(GRAPH_COLORS, self._expressions()):
            parts = split_numbers(src)
            if len(parts) != 2:
                raise CalcError("Write each curve as   x(t), y(t)")
            fx, fy = (self.engine.compile(p, params=("t",)) for p in parts)
            xs, ys = self._eval_on(fx, ("t",), ts), self._eval_on(fy, ("t",), ts)
            nan = lambda v: math.nan if v is None else v
            ax.plot([nan(x) if y is not None else math.nan for x, y in zip(xs, ys)], [nan(y) for y in ys],
                    color=color, linewidth=2, label=src)
        ax.axhline(0, color=c["axis"], linewidth=1.0)
        ax.axvline(0, color=c["axis"], linewidth=1.0)
        ax.set_aspect("equal", adjustable="datalim")  # a circle should look like a circle
        self._legend(ax)

    def _y_range(self, series, log=False):
        """y limits: the ymin/ymax fields if given, else the middle 96% of the values plus padding.
        Worked out in screen space (log10 for a log axis), so padding is even on both scales."""
        try:
            ymin, ymax = self._graph_number("ymin"), self._graph_number("ymax")
            if ymin is not None and ymax is not None and ymax > ymin:
                return ymin, ymax
        except CalcError:
            pass
        to_u, from_u = self._scale_fns(log)
        values = sorted(to_u(v) for s in series for v in s if v is not None and (v > 0 or not log))
        if values:  # ignore the extreme 2% on each side so asymptotes don't flatten everything
            lo, hi = values[int(0.02 * (len(values) - 1))], values[int(0.98 * (len(values) - 1))]
        else:
            lo, hi = (-1, 1)
        if hi - lo < 1e-9:
            lo, hi = lo - 1, hi + 1
        pad = (hi - lo) * 0.08
        return from_u(lo - pad), from_u(hi + pad)

    # ---- Matplotlib events: trace, zoom, pan
    def _mpl_cache_background(self, e):
        self._mpl.bg = self._mpl.canvas.copy_from_bbox(self._mpl.fig.bbox)

    def _mpl_hide_trace(self):
        m = self._mpl
        if m and m.bg is not None and self._pl:
            m.canvas.restore_region(m.bg)
            m.canvas.blit(m.fig.bbox)

    def _mpl_motion(self, e):
        m, st = self._mpl, self._pl
        if GRAPH_MODES[self._g_mode]["draw"] != "_draw_function":
            return  # no trace here; and blitting a cached frame would fight 3D rotation redraws
        if self._drag:
            return self._mpl_drag(e)
        if not st or not st["funcs"] or e.inaxes is not m.ax or m.bg is None:
            return self._mpl_hide_trace()
        x = e.xdata
        try:
            with self.engine.angle_mode(False):
                y = float(st["funcs"][0].eval({"x": x}))
        except (CalcError, OverflowError):
            y = None
        m.canvas.restore_region(m.bg)
        m.vline.set_xdata([x, x])
        m.dot.set_data([x] if y is not None else [], [y] if y is not None else [])
        m.label.set_text(f"x = {x:.4g}" + (f"   y = {y:.4g}" if y is not None else "   y undefined"))
        for artist in (m.vline, m.dot, m.label):
            m.ax.draw_artist(artist)
        m.canvas.blit(m.fig.bbox)

    def _mpl_scroll(self, e):
        st = self._pl
        if not st or e.inaxes is not self._mpl.ax:
            return
        factor = 0.8 if e.button == "up" else 1.25
        view = []
        # zoom in screen space (log10 on a log axis), keeping the point under the pointer fixed
        for lo, hi, at, log in ((st["xmin"], st["xmax"], e.xdata, st["logx"]), (st["ymin"], st["ymax"], e.ydata, st["logy"])):
            to_u, from_u = self._scale_fns(log)
            u0, u1, ua = to_u(lo), to_u(hi), to_u(at)
            span = (u1 - u0) * factor
            if not 1e-9 < span < (300 if log else 1e12):
                return  # beyond this, float precision or overflow makes the plot meaningless
            f = (ua - u0) / (u1 - u0)
            view += [from_u(ua - f * span), from_u(ua + (1 - f) * span)]
        self._set_view(*view)

    def _mpl_press(self, e):
        if e.button != 1 or e.inaxes is not self._mpl.ax or not self._pl:
            return
        if e.dblclick:
            return self._reset_view()
        box = self._mpl.ax.bbox
        self._drag = (e.x, e.y, dict(self._pl), box.width, box.height)
        self._mpl.widget.configure(cursor="fleur")

    def _mpl_drag(self, e):
        x0, y0, st, w, h = self._drag
        view = []
        # pan in screen space, so a log axis moves by whole decades evenly (Matplotlib's y grows upwards)
        for lo, hi, moved, size, log in ((st["xmin"], st["xmax"], e.x - x0, w, st["logx"]),
                                         (st["ymin"], st["ymax"], e.y - y0, h, st["logy"])):
            to_u, from_u = self._scale_fns(log)
            u0, u1 = to_u(lo), to_u(hi)
            du = moved / size * (u1 - u0)
            view += [from_u(u0 - du), from_u(u1 - du)]
        self._set_view(*view)

    def _mpl_release(self, e):
        if self._drag:
            self._drag = None
            self._mpl.widget.configure(cursor="crosshair")

    # ================= tools tab ============================================ #
    def _card(self, parent, title):
        card = ctk.CTkFrame(parent, corner_radius=12)
        card.pack(fill="x", padx=6, pady=6)
        ctk.CTkLabel(card, text=title, font=ctk.CTkFont(size=16, weight="bold")).pack(anchor="w", padx=12, pady=(10, 4))
        return card

    def _row(self, card):
        r = ctk.CTkFrame(card, fg_color="transparent")
        r.pack(fill="x", padx=10, pady=3)
        return r

    def _out_label(self, card):
        lab = ctk.CTkLabel(card, text="", justify="left", anchor="w", wraplength=760,
                           font=ctk.CTkFont(family=MONO, size=13))
        lab.pack(fill="x", padx=14, pady=(2, 10))
        return lab

    def _labeled_entry(self, row, label, width, default=""):
        ctk.CTkLabel(row, text=label).pack(side="left", padx=(8, 2))
        en = ctk.CTkEntry(row, width=width)
        en.insert(0, default)
        en.pack(side="left")
        return en

    def _build_tools_tab(self):
        sc = ctk.CTkScrollableFrame(self.tabs.tab("Tools"), fg_color="transparent")
        sc.pack(fill="both", expand=True)

        # --- base converter
        card = self._card(sc, "🔢 Base converter")
        r = self._row(card)
        self.base_in = ctk.CTkEntry(r, width=240, placeholder_text="e.g. 255, ff, 1010, 0x1f")
        self.base_in.pack(side="left", padx=4)
        self.base_in.bind("<KeyRelease>", lambda e: self._convert_base())
        self.base_from = GlideOptionMenu(r, values=["Decimal (10)", "Binary (2)", "Octal (8)", "Hex (16)"],
                                           width=150, command=lambda _: self._convert_base())
        self.base_from.pack(side="left", padx=4)
        self.base_out = self._out_label(card)

        # --- unit converter
        card = self._card(sc, "📏 Unit converter")
        r = self._row(card)
        self.unit_val = ctk.CTkEntry(r, width=120)
        self.unit_val.insert(0, "1")
        self.unit_val.pack(side="left", padx=4)
        self.unit_val.bind("<KeyRelease>", self._convert_unit)
        self.unit_cat = GlideOptionMenu(r, values=list(UNITS), width=130, command=self._unit_category)
        self.unit_cat.pack(side="left", padx=4)
        self.unit_from = GlideOptionMenu(r, values=list(UNITS["Length"]), width=100, command=self._convert_unit)
        self.unit_from.pack(side="left", padx=4)
        ctk.CTkLabel(r, text="→").pack(side="left")
        self.unit_to = GlideOptionMenu(r, values=list(UNITS["Length"]), width=100, command=self._convert_unit)
        self.unit_to.pack(side="left", padx=4)
        RippleButton(r, text="⇄", width=36, command=self._swap_units).pack(side="left", padx=4)
        self.unit_out = self._out_label(card)
        self._unit_category("Length")

        # --- number lab
        card = self._card(sc, "🔬 Number lab")
        r = self._row(card)
        self.nl_in = ctk.CTkEntry(r, width=240, placeholder_text="a whole number, e.g. 360360")
        self.nl_in.pack(side="left", padx=4)
        self.nl_in.bind("<Return>", lambda e: self._number_lab())
        RippleButton(r, text="Analyze", width=90, command=self._number_lab).pack(side="left", padx=4)
        self.nl_out = self._out_label(card)

        # --- statistics
        card = self._card(sc, "📊 Statistics")
        r = self._row(card)
        self.st_in = ctk.CTkEntry(r, width=420, placeholder_text="numbers separated by commas: 4, 8, 15, 16, 23, 42")
        self.st_in.pack(side="left", padx=4)
        self.st_in.bind("<Return>", lambda e: self._stats())
        RippleButton(r, text="Compute", width=90, command=self._stats).pack(side="left", padx=4)
        self.st_out = self._out_label(card)

        # --- calculus lab
        card = self._card(sc, "∫ Calculus lab  (numeric derivative · integral · root, trig in radians)")
        r = self._row(card)
        self.cal_f = self._labeled_entry(r, "f(x) =", 240, "x^3 - 2*x - 5")
        self.cal_a = self._labeled_entry(r, "a", 70, "2")
        self.cal_b = self._labeled_entry(r, "b", 70, "3")
        r2 = self._row(card)
        for text, mode in (("f'(a)", "d"), ("∫ a → b", "i"), ("Find root", "r")):
            RippleButton(r2, text=text, width=90, command=lambda m=mode: self._calculus(m)).pack(side="left", padx=4)
        self.cal_out = self._out_label(card)

    # ---- base converter
    def _convert_base(self):
        text = self.base_in.get().strip().replace("_", "").replace(" ", "")
        if not text:
            self.base_out.configure(text="", text_color=TEXT)
            return
        base = int(re.search(r"\((\d+)\)", self.base_from.get()).group(1))
        if re.fullmatch(r"-?0[xXbBoO]\w+", text):
            base = 0  # an explicit 0x / 0b / 0o prefix wins over the menu
        try:
            n = int(text, base)
            lines = [f"Decimal : {n}", f"Binary  : {bin(n)}", f"Octal   : {oct(n)}", f"Hex     : {hex(n)}"]
        except ValueError:
            self.base_out.configure(text=f"'{text}' is not a valid base-{base or 'prefixed'} number", text_color=RED)
            return
        if 32 <= n < 127:
            lines.append(f"ASCII   : '{chr(n)}'")
        self.base_out.configure(text="\n".join(lines), text_color=TEXT)

    # ---- unit converter
    def _unit_category(self, cat):
        units = list(UNITS[cat])
        self.unit_from.configure(values=units)
        self.unit_to.configure(values=units)
        self.unit_from.set(units[0])
        self.unit_to.set(units[1])
        self._convert_unit()

    def _swap_units(self):
        a, b = self.unit_from.get(), self.unit_to.get()
        self.unit_from.set(b)
        self.unit_to.set(a)
        self._convert_unit()

    def _convert_unit(self, *_):
        cat, a, b = self.unit_cat.get(), self.unit_from.get(), self.unit_to.get()
        try:
            v = self.engine.evaluate(self.unit_val.get())
            out = convert_unit(v, cat, a, b)
        except (CalcError, OverflowError):
            self.unit_out.configure(text="—", text_color=MUTED)
            return
        self.unit_out.configure(text=f"{fmt(v)} {a}  =  {fmt(out, 10)} {b}", text_color=TEXT)

    # ---- number lab
    def _number_lab(self):
        try:
            n = _as_int(self.engine.evaluate(self.nl_in.get()), "Input")
        except CalcError as ex:
            self.nl_out.configure(text=f"⚠ {ex}", text_color=RED)
            return
        if abs(n) > FACTOR_LIMIT_LAB:
            self.nl_out.configure(text="⚠ Please use a number up to 10^20", text_color=RED)
            return
        a = abs(n)
        digits = str(a)
        lines = [f"Number         : {n}", f"Prime?         : {'yes ✨' if is_prime(a) else 'no'}"]
        if a >= 2:
            f = factorize(a)
            dcount, dsum = 1, 1
            for p, e in f.items():
                dcount *= e + 1
                dsum *= (p ** (e + 1) - 1) // (p - 1)
            pp = prev_prime(a)
            lines += [f"Factorization  : {factor_str(f)}",
                      f"Divisors       : {dcount} (sum {dsum})",
                      f"Next prime     : {next_prime(a)}",
                      f"Previous prime : {pp if pp else '—'}"]
        r = math.isqrt(a)
        is_fib = any(math.isqrt(x) ** 2 == x for x in (5 * a * a + 4, 5 * a * a - 4) if x >= 0)
        lines += [f"Perfect square : {'yes (' + str(r) + '²)' if r * r == a else 'no'}",
                  f"Digit sum      : {sum(map(int, digits))}",
                  f"Reversed       : {digits[::-1]}",
                  f"Palindrome     : {'yes' if digits == digits[::-1] else 'no'}",
                  f"Fibonacci num  : {'yes' if is_fib else 'no'}"]
        self.nl_out.configure(text="\n".join(lines), text_color=TEXT)

    # ---- statistics
    def _stats(self):
        try:
            data = [self.engine.evaluate(t) for t in split_numbers(self.st_in.get())]
            if not data:
                raise CalcError("Enter some numbers first")
            lo, hi = min(data), max(data)
            lines = [f"Count     : {len(data)}", f"Sum       : {fmt(sum(data))}",
                     f"Mean      : {fmt(statistics.mean(data))}", f"Median    : {fmt(statistics.median(data))}",
                     f"Mode      : {', '.join(fmt(m) for m in statistics.multimode(data)[:5])}",
                     f"Min / Max : {fmt(lo)} / {fmt(hi)}   (range {fmt(hi - lo)})",
                     f"Std dev   : population {fmt(statistics.pstdev(data))}"
                     + (f", sample {fmt(statistics.stdev(data))}" if len(data) > 1 else "")]
        except (CalcError, OverflowError) as ex:
            msg = str(ex) if isinstance(ex, CalcError) else "Numbers too large"
            self.st_out.configure(text=f"⚠ {msg}", text_color=RED)
            return
        self.st_out.configure(text="\n".join(lines), text_color=TEXT)

    # ---- calculus
    def _calculus(self, mode):
        try:
            fx = self.engine.compile(strip_lhs(self.cal_f.get()), params=("x",))
            scope = {}

            def f(x):
                scope["x"] = x
                return float(fx.eval(scope))

            a = float(self.engine.evaluate(self.cal_a.get() or "0"))
            b = float(self.engine.evaluate(self.cal_b.get() or "1"))
            with self.engine.angle_mode(False):
                if mode == "d":
                    msg = f"f'({fmt(a)}) ≈ {fmt(round(derivative(f, a), 8))}"
                elif mode == "i":
                    msg = f"∫ from {fmt(a)} to {fmt(b)} of f(x) dx ≈ {fmt(round(integrate(f, a, b), 8))}"
                else:
                    found = find_root(f, a, b)
                    if found is None:
                        msg = "No root found - try other starting values (or a bracket where f changes sign)"
                    elif found[1] == "newton":
                        msg = f"Root near {fmt(a)} (Newton): x ≈ {fmt(round(found[0], 10))}"
                    else:
                        msg = f"Root in [{fmt(a)}, {fmt(b)}]: x ≈ {fmt(round(found[0], 10))}"
            self.cal_out.configure(text=msg, text_color=TEXT)
        except CalcError as ex:
            self.cal_out.configure(text=f"⚠ {ex}", text_color=RED)
        except Exception:
            self.cal_out.configure(text="⚠ Could not evaluate f(x) there", text_color=RED)

    # ================= challenge tab ======================================== #
    def _build_challenge_tab(self):
        t = self.tabs.tab("Challenge")
        self.q = None
        self.score = self.total = self.streak = self.best = 0
        self.times = []

        top = ctk.CTkFrame(t, fg_color="transparent")
        top.pack(fill="x", padx=8, pady=8)
        self.ch_mode = GlideSegments(top, ["Solve it", "Right or Wrong?"], command=lambda _: self._new_question())
        self.ch_mode.set("Right or Wrong?", animate=False)
        self.ch_mode.pack(side="left", padx=6)
        self.ch_level = GlideSegments(top, ["Easy", "Medium", "Hard"], command=lambda _: self._new_question())
        self.ch_level.pack(side="left", padx=6)
        RippleButton(top, text="Reset score", width=100, command=self._reset_score).pack(side="right", padx=6)

        self.q_label = ctk.CTkLabel(t, text="", font=ctk.CTkFont(family=MONO, size=38, weight="bold"))
        self.q_label.pack(pady=(50, 20))

        self.solve_box = ctk.CTkFrame(t, fg_color="transparent")
        self.q_entry = ctk.CTkEntry(self.solve_box, width=220, height=46, justify="center",
                                    font=ctk.CTkFont(family=MONO, size=22))
        self.q_entry.pack(side="left", padx=6)
        self.q_entry.bind("<Return>", lambda e: self._answer_solve())
        RippleButton(self.solve_box, text="Submit", height=46, command=self._answer_solve).pack(side="left", padx=6)

        self.rw_box = ctk.CTkFrame(t, fg_color="transparent")
        RippleButton(self.rw_box, text="✔  Right", width=180, height=56, font=ctk.CTkFont(size=20, weight="bold"),
                      fg_color=(GREEN, "#106A43"), hover_color=("#25855D", "#0D5636"),
                      command=lambda: self._answer_rw(True)).pack(side="left", padx=12)
        RippleButton(self.rw_box, text="✘  Wrong", width=180, height=56, font=ctk.CTkFont(size=20, weight="bold"),
                      fg_color=(RED, "#A33A36"), hover_color=("#C23A3F", "#872F2B"),
                      command=lambda: self._answer_rw(False)).pack(side="left", padx=12)

        self.ch_feedback = ctk.CTkLabel(t, text="", font=ctk.CTkFont(size=20, weight="bold"))
        self.ch_feedback.pack(pady=18)
        self.ch_stats = ctk.CTkLabel(t, text="", text_color=MUTED, font=ctk.CTkFont(family=MONO, size=14))
        self.ch_stats.pack()
        self._pending = None
        self._new_question()

    def _reset_score(self):
        self.score = self.total = self.streak = self.best = 0
        self.times = []
        self._update_stats()
        self._new_question()

    @staticmethod
    def _gen(level):
        r = random.randint
        if level == "Easy":
            return f"{r(2, 20)} {random.choice('+-*')} {r(2, 20)}"
        if level == "Medium":
            a, b, c = r(3, 15), r(3, 15), r(2, 30)
            return random.choice([f"{a} * {b}", f"{a * b} / {b}", f"{a}^2 + {b}", f"{a} * {b} - {c}",
                                  f"({a} + {b}) * {c}", f"{r(2, 9)}^{r(2, 4)} + {c}"])
        n, m = r(5, 8), r(2, 4)
        return random.choice([f"{r(3, 8)}!", f"{r(2, 9)}^{r(2, 4)} - {r(10, 99)}",
                              f"sqrt({r(2, 25) ** 2}) * {r(3, 15)}", f"ncr({r(5, 12)}, {r(2, 4)})",
                              f"{n}! / {m}!", f"({r(2, 9)} + {r(2, 9)})^2 - {r(5, 40)}"])

    @staticmethod
    def _pretty(expr):
        return expr.replace("*", "×").replace("/", "÷")

    def _new_question(self):
        if self._pending:
            self.after_cancel(self._pending)
            self._pending = None
        expr = self._gen(self.ch_level.get())
        ans = self.quiz_engine.evaluate(expr)
        if self.ch_mode.get() == "Right or Wrong?":
            shown = ans
            if random.random() < 0.5:
                delta = random.choice([-10, -3, -2, -1, 1, 2, 3, 10])
                shown = ans + delta if isinstance(ans, int) else round(ans + delta, 2)
            self.solve_box.pack_forget()
            self.rw_box.pack(after=self.q_label)
            text = f"{self._pretty(expr)} = {fmt(shown)}"
            truth = self.quiz_engine.process(f"{expr} = {shown}").ok  # the validator is the referee
        else:
            self.rw_box.pack_forget()
            self.solve_box.pack(after=self.q_label)
            text = self._pretty(expr) + " = ?"
            truth = None
            self.q_entry.delete(0, "end")
            if self.tabs.get() == "Challenge":  # don't steal focus from another tab
                self.q_entry.focus_set()
        self.q = {"expr": expr, "answer": ans, "truth": truth, "t0": time.perf_counter(), "done": False}
        self.q_label.configure(text=text)
        self.ch_feedback.configure(text="")
        self._update_stats()

    def _answer_solve(self):
        if not self.q or self.q["done"]:
            return
        try:
            val = self.quiz_engine.evaluate(self.q_entry.get())
        except CalcError:
            self.ch_feedback.configure(text="Type a number (expressions work too)", text_color=MUTED)
            return
        self._grade(close(val, self.q["answer"]), f"Answer: {fmt(self.q['answer'])}")

    def _answer_rw(self, says_right):
        if not self.q or self.q["done"]:
            return
        self._grade(says_right == self.q["truth"], f"True value: {fmt(self.q['answer'])}")

    def _grade(self, ok, reveal):
        self.q["done"] = True
        self.total += 1
        self.times.append(time.perf_counter() - self.q["t0"])
        if ok:
            self.score += 1
            self.streak += 1
            self.best = max(self.best, self.streak)
            self.ch_feedback.configure(text="✔ Correct!" + (f"  🔥 {self.streak} in a row" if self.streak >= 3 else ""), text_color=GREEN)
        else:
            self.streak = 0
            self.ch_feedback.configure(text=f"✘ Not quite.  {reveal}", text_color=RED)
        self._update_stats()
        self._pending = self.after(1300, self._new_question)

    def _update_stats(self):
        avg = f"{sum(self.times) / len(self.times):.1f}s" if self.times else "—"
        self.ch_stats.configure(text=f"Score {self.score}/{self.total}    Streak {self.streak}    Best {self.best}    Avg time {avg}")


# --------------------------------------------------------------------------- #
#  Entry points
# --------------------------------------------------------------------------- #
def describe_result(out: Result) -> str:
    """Plain-text rendering of an engine result (used by the CLI)."""
    if isinstance(out, ValueResult):
        return fmt(out.value)
    if isinstance(out, Assignment):
        return f"{out.name} = {fmt(out.value)}"
    if isinstance(out, FunctionDef):
        return f"{out.name}({', '.join(out.params)}) = {out.body}   (function stored)"
    chain = fmt(out.values[0]) + "".join(f" {op} {fmt(v)}" for op, v in zip(out.ops, out.values[1:]))
    return f"{'✔ Correct' if out.ok else '✘ Wrong'}   ({chain})"


def run_repl(engine: Engine):
    print("UltraCalc REPL - type an expression, 'deg'/'rad' to switch angles, 'quit' to exit.")
    while True:
        try:
            line = input("» ").strip()
        except (EOFError, KeyboardInterrupt):
            print()
            return
        if line in ("quit", "exit", "q"):
            return
        if line in ("deg", "rad"):
            engine.deg = line == "deg"
            print(f"angle mode: {line.upper()}")
            continue
        if not line:
            continue
        try:
            print(describe_result(engine.process(line)))
        except CalcError as ex:
            print(f"Error: {ex}")


def run_gui():
    if ctk is None:
        raise SystemExit("The GUI needs tkinter and customtkinter:  pip install customtkinter")
    ctk.set_default_color_theme("blue")  # the saved light/dark theme is applied by UltraCalc itself
    UltraCalc().mainloop()


def main(argv=None):
    parser = argparse.ArgumentParser(description="UltraCalc - calculator, validator and grapher.")
    parser.add_argument("expressions", nargs="*", help="evaluate these and print the results (no GUI)")
    parser.add_argument("--repl", action="store_true", help="interactive terminal mode")
    parser.add_argument("--rad", action="store_true", help="use radians instead of degrees")
    args = parser.parse_args(argv)

    if not args.expressions and not args.repl:
        run_gui()
        return 0
    engine = Engine(deg=not args.rad)
    status = 0
    for expr in args.expressions:
        try:
            print(describe_result(engine.process(expr)))
        except CalcError as ex:
            print(f"Error: {ex}", file=sys.stderr)
            status = 1
    if args.repl:
        run_repl(engine)
    return status


if __name__ == "__main__":
    sys.exit(main())
