"""
UltraCalc - a feature-packed calculator built with customtkinter.

Setup:   pip install customtkinter
Run:     python ultracalc.py

Highlights
  * Safe expression engine (no eval): + - * / // mod ^ ! % () functions, constants, variables
  * Equation VALIDATOR: type  1+1=11  ->  Wrong,  5!=120  ->  Correct  (also < > <= >= and chains)
  * Live preview while you type, history (saved between runs), memory, ANS, DEG/RAD
  * Function grapher with hover trace, base/unit converters, number lab, statistics, calculus lab
  * Math Challenge game (solve it / spot right-or-wrong) with streaks
"""
import ast
import json
import math
import operator
import os
import random
import re
import statistics
import sys
import time
import tkinter as tk
from datetime import datetime
from fractions import Fraction
from tkinter import filedialog

import customtkinter as ctk

# --------------------------------------------------------------------------- #
#  Constants & small helpers
# --------------------------------------------------------------------------- #
MONO = ("Consolas" if sys.platform.startswith("win")
        else "Menlo" if sys.platform == "darwin" else "DejaVu Sans Mono")
GREEN, RED = "#2FA572", "#E5484D"
TEXT = ("gray10", "gray92")
MUTED = ("gray45", "gray60")
HISTORY_FILE = os.path.join(os.path.expanduser("~"), ".ultracalc_history.json")
SUP = str.maketrans("0123456789", "⁰¹²³⁴⁵⁶⁷⁸⁹")

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
    "Temperature": {"°C": 0, "°F": 0, "K": 0},
}


class CalcError(Exception):
    """Any user-facing calculation problem."""


def close(a, b):
    return math.isclose(a, b, rel_tol=1e-9, abs_tol=1e-12)


def is_prime(n):
    if n < 2:
        return False
    small = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
    for p in small:
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in small:
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


def next_prime(n):
    n += 1
    while not is_prime(n):
        n += 1
    return n


def prev_prime(n):
    n -= 1
    while n >= 2 and not is_prime(n):
        n -= 1
    return n if n >= 2 else None


def factorize(n):
    n, out, d = abs(n), {}, 2
    while d * d <= n:
        while n % d == 0:
            out[d] = out.get(d, 0) + 1
            n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def factor_str(f):
    return " × ".join(f"{p}{str(e).translate(SUP)}" if e > 1 else str(p)
                      for p, e in sorted(f.items()))


def fmt(v, digits=12):
    """Pretty number formatting."""
    if isinstance(v, bool):
        return str(int(v))
    if isinstance(v, int):
        s = str(abs(v))
        if len(s) > 30:
            sign = "-" if v < 0 else ""
            return f"{sign}{s[0]}.{s[1:11]}e+{len(s) - 1}"
        return str(v)
    if isinstance(v, float):
        if v.is_integer() and abs(v) < 1e15:
            return str(int(v))
        return f"{v:.{digits}g}"
    return str(v)


def insights(v):
    """Small extra info shown under the result."""
    try:
        if isinstance(v, float) and v.is_integer() and abs(v) < 1e15:
            v = int(v)
        if isinstance(v, int):
            a, sign, out = abs(v), "-" if v < 0 else "", []
            if len(str(a)) > 15:
                out.append(f"{len(str(a))} digits")
            if a < 2 ** 64:
                out.append(f"bin {sign}{bin(a)[2:]}   hex {sign}{hex(a)[2:]}")
            if 2 <= a <= 10 ** 13:
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
def _as_int(x, what="value"):
    if isinstance(x, float):
        if not x.is_integer():
            raise CalcError(f"{what} must be a whole number")
        x = int(x)
    return x


def fact(x):
    if isinstance(x, float) and not x.is_integer():
        if x > 170:
            raise CalcError("Factorial too large")
        return math.gamma(x + 1)
    n = int(x)
    if n < 0:
        raise CalcError("Factorial of a negative integer is undefined")
    if n > 5000:
        raise CalcError("Factorial too large (max 5000!)")
    return math.factorial(n)


def fib(n):
    n = _as_int(n, "n")
    if n < 0 or n > 20000:
        raise CalcError("fib(n) needs 0 <= n <= 20000")
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


def _round(x, n=0):
    n = int(n)
    f = 10 ** n
    r = math.floor(x * f + 0.5) / f
    return int(r) if n <= 0 else r


def _cbrt(x):
    res = math.copysign(abs(x) ** (1 / 3), x)
    r = round(res)
    return r if r ** 3 == x else res


def _root(x, n):
    n = _as_int(n, "root degree")
    if n == 0:
        raise CalcError("Root degree cannot be 0")
    if x < 0 and n % 2 == 0:
        raise CalcError("Even root of a negative number")
    res = math.copysign(abs(x) ** (1 / n), x)
    r = round(res)
    return r if r ** n == x else res


# --------------------------------------------------------------------------- #
#  The engine: safe parsing + evaluation + validation
# --------------------------------------------------------------------------- #
CMP_SPLIT = re.compile(r"(<=|>=|≠|<>|==|≤|≥|=|<|>)")
IMPLICIT = re.compile(r"((?<![A-Za-z_\d.])\d+\.?\d*(?![eE][+-]?\d)|\))\s*(?=[A-Za-z_(])")
BIN_OPS = {ast.Add: operator.add, ast.Sub: operator.sub, ast.Mult: operator.mul,
           ast.Div: operator.truediv, ast.FloorDiv: operator.floordiv,
           ast.Mod: operator.mod, ast.Pow: operator.pow}


class Engine:
    def __init__(self):
        self.deg = True
        self.vars = {}
        self.ans = 0
        self.memory = 0
        self.funcs = self._build_funcs()
        self.reserved = set(CONSTS) | set(self.funcs) | {"ans", "m", "let"}

    # ---- function table ------------------------------------------------- #
    def _build_funcs(self):
        def tr(f):
            return lambda x: round(f(math.radians(x) if self.deg else x), 12) + 0.0

        def itr(f):
            return lambda x: math.degrees(f(x)) if self.deg else f(x)

        def sqrt(x):
            if x < 0:
                raise CalcError("Square root of a negative number")
            if isinstance(x, int):
                r = math.isqrt(x)
                if r * r == x:
                    return r
            return math.sqrt(x)

        def ints(f, a, b):
            return f(_as_int(a), _as_int(b))

        return {
            "sin": tr(math.sin), "cos": tr(math.cos), "tan": tr(math.tan),
            "asin": itr(math.asin), "acos": itr(math.acos), "atan": itr(math.atan),
            "sinh": math.sinh, "cosh": math.cosh, "tanh": math.tanh,
            "sqrt": sqrt, "cbrt": _cbrt, "root": _root, "abs": abs,
            "log": math.log10, "ln": math.log, "log2": math.log2,
            "logb": lambda x, b: math.log(x, b), "exp": math.exp,
            "floor": math.floor, "ceil": math.ceil, "round": _round,
            "sign": lambda x: (x > 0) - (x < 0), "pow": lambda a, b: self._pow(a, b),
            "fact": fact, "fib": fib,
            "ncr": lambda n, r: ints(math.comb, n, r),
            "npr": lambda n, r: ints(math.perm, n, r),
            "gcd": lambda a, b: ints(math.gcd, a, b),
            "lcm": lambda a, b: ints(math.lcm, a, b),
            "isprime": lambda n: int(is_prime(_as_int(n))),
            "nextprime": lambda n: next_prime(_as_int(n)),
            "hypot": math.hypot, "rad": math.radians, "deg": math.degrees,
            "mean": lambda *a: statistics.mean(a),
            "median": lambda *a: statistics.median(a),
            "stdev": lambda *a: statistics.stdev(a),
            "sum": lambda *a: sum(a), "max": lambda *a: max(a), "min": lambda *a: min(a),
            "rand": lambda: random.random(),
            "randint": lambda a, b: random.randint(_as_int(a), _as_int(b)),
        }

    # ---- text -> python expression -------------------------------------- #
    def prepare(self, s):
        s = s.strip()
        s = re.sub(r"[√∛]\s*(\d+(?:\.\d+)?|[A-Za-z_]\w*)",
                   lambda m: ("sqrt(" if m.group(0)[0] == "√" else "cbrt(") + m.group(1) + ")", s)
        for k, v in {"×": "*", "÷": "/", "−": "-", "–": "-", "√": "sqrt", "∛": "cbrt",
                     "π": "pi", "τ": "tau", "φ": "phi", "²": "**2", "³": "**3",
                     "^": "**", "\u00a0": " "}.items():
            s = s.replace(k, v)
        if s.count("(") != s.count(")"):
            raise CalcError("Unbalanced parentheses")
        s = re.sub(r"(\d+(?:\.\d+)?)\s*%(?!\s*[\d(A-Za-z_])", r"(\1/100)", s)
        s = re.sub(r"\bmod\b", "%", s)
        s = self._expand_factorials(s)
        s = IMPLICIT.sub(r"\1*", s)
        return s

    @staticmethod
    def _expand_factorials(s):
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

    def compile(self, expr):
        py = self.prepare(expr)
        if not py:
            raise CalcError("Empty expression")
        try:
            return ast.parse(py, mode="eval")
        except SyntaxError:
            raise CalcError("Syntax error - check your expression")
        except (RecursionError, MemoryError):
            raise CalcError("Expression too complex")

    # ---- evaluation ------------------------------------------------------ #
    def evaluate(self, expr, extra=None):
        return self.eval_tree(self.compile(expr), extra)

    def eval_tree(self, tree, extra=None):
        try:
            v = self._ev(tree, extra or {})
        except CalcError:
            raise
        except ZeroDivisionError:
            raise CalcError("Division by zero")
        except OverflowError:
            raise CalcError("Result too large")
        except ValueError:
            raise CalcError("Math domain error")
        except TypeError:
            raise CalcError("Wrong arguments for a function")
        except statistics.StatisticsError:
            raise CalcError("Not enough data points")
        except RecursionError:
            raise CalcError("Expression too deeply nested")
        if isinstance(v, complex):
            raise CalcError("Complex results are not supported")
        if isinstance(v, float) and (math.isnan(v) or math.isinf(v)):
            raise CalcError("Undefined result")
        return v

    def _pow(self, a, b):
        if a == 0 and b < 0:
            raise CalcError("Division by zero")
        if a < 0 and not float(b).is_integer():
            raise CalcError("Complex results are not supported")
        if abs(b) > 100000 or (abs(a) > 1 and abs(b) * math.log10(abs(a)) > 5000):
            raise CalcError("Result too large")
        return a ** b

    def _ev(self, n, extra):
        if isinstance(n, ast.Expression):
            return self._ev(n.body, extra)
        if isinstance(n, ast.Constant):
            if isinstance(n.value, (int, float)) and not isinstance(n.value, bool):
                return n.value
            raise CalcError("Unsupported value")
        if isinstance(n, ast.BinOp):
            op = type(n.op)
            if op not in BIN_OPS:
                raise CalcError("Unsupported operator")
            a, b = self._ev(n.left, extra), self._ev(n.right, extra)
            if op is ast.Pow:
                return self._pow(a, b)
            if op is ast.Div:
                if b == 0:
                    raise CalcError("Division by zero")
                if isinstance(a, int) and isinstance(b, int) and a % b == 0:
                    return a // b
                return a / b
            if op in (ast.Mod, ast.FloorDiv) and b == 0:
                raise CalcError("Division by zero")
            return BIN_OPS[op](a, b)
        if isinstance(n, ast.UnaryOp):
            v = self._ev(n.operand, extra)
            if isinstance(n.op, ast.USub):
                return -v
            if isinstance(n.op, ast.UAdd):
                return +v
            raise CalcError("Unsupported operator")
        if isinstance(n, ast.Name):
            k = n.id
            if k in extra:
                return extra[k]
            if k in self.vars:
                return self.vars[k]
            if k in CONSTS:
                return CONSTS[k]
            if k == "ans":
                return self.ans
            if k == "m":
                return self.memory
            raise CalcError(f"Unknown name '{k}'")
        if isinstance(n, ast.Call):
            if not isinstance(n.func, ast.Name) or n.keywords:
                raise CalcError("Unsupported function call")
            f = self.funcs.get(n.func.id)
            if f is None:
                raise CalcError(f"Unknown function '{n.func.id}'")
            return f(*[self._ev(a, extra) for a in n.args])
        raise CalcError("Unsupported syntax")

    # ---- top level: value / assignment / validation ----------------------- #
    def process(self, raw, commit=True):
        raw = raw.strip()
        if not raw:
            raise CalcError("Empty expression")

        m = (re.match(r"^let\s+([A-Za-z_]\w*)\s*(?::=|=)\s*(.+)$", raw)
             or re.match(r"^([A-Za-z_]\w*)\s*:=\s*(.+)$", raw))
        if m:
            name, rhs = m.group(1), m.group(2)
            if name in self.reserved:
                raise CalcError(f"'{name}' is a reserved name")
            val = self.evaluate(rhs)
            if commit:
                self.vars[name] = val
            return {"kind": "assign", "name": name, "value": val}

        parts = CMP_SPLIT.split(raw)
        if len(parts) > 1:
            exprs, ops = parts[0::2], parts[1::2]
            if len(ops) == 1 and not exprs[1].strip() and exprs[0].strip():
                return {"kind": "value", "value": self.evaluate(exprs[0])}
            if any(not e.strip() for e in exprs):
                raise CalcError("Missing value next to a comparison sign")
            vals = [self.evaluate(e) for e in exprs]
            ok = all(self._cmp(vals[i], op, vals[i + 1]) for i, op in enumerate(ops))
            return {"kind": "check", "ok": ok, "exprs": exprs, "ops": ops, "values": vals}

        return {"kind": "value", "value": self.evaluate(raw)}

    @staticmethod
    def _cmp(a, op, b):
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


# --------------------------------------------------------------------------- #
#  Graph helper
# --------------------------------------------------------------------------- #
def nice_step(span, target=8):
    raw = span / target
    mag = 10 ** math.floor(math.log10(raw))
    for m in (1, 2, 5, 10):
        if raw <= m * mag:
            return m * mag
    return 10 * mag


GRAPH_COLORS = ["#4EA1FF", "#FF6B6B", "#2FD38E", "#FFB020", "#B36BFF"]


# --------------------------------------------------------------------------- #
#  The app
# --------------------------------------------------------------------------- #
class UltraCalc(ctk.CTk):
    def __init__(self):
        super().__init__()
        self.title("UltraCalc")
        self.geometry("1160x800")
        self.minsize(1000, 700)

        self.engine = Engine()
        self.quiz_engine = Engine()
        self.history = []
        self.hist_idx = None
        self.last_text = ""
        self._pl = None

        self.grid_columnconfigure(0, weight=1)
        self.grid_rowconfigure(1, weight=1)

        self._build_header()
        self.tabs = ctk.CTkTabview(self)
        self.tabs.grid(row=1, column=0, sticky="nsew", padx=(10, 6), pady=(0, 10))
        for name in ("Calculator", "Graph", "Tools", "Challenge"):
            self.tabs.add(name)
        self._build_calc_tab()
        self._build_graph_tab()
        self._build_tools_tab()
        self._build_challenge_tab()
        self._build_sidebar()

        self._load_history()
        self.protocol("WM_DELETE_WINDOW", self._on_close)
        self.after(150, self.entry.focus_set)
        self.after(250, self.plot)

    # ================= header ============================================== #
    def _build_header(self):
        h = ctk.CTkFrame(self, fg_color="transparent")
        h.grid(row=0, column=0, columnspan=2, sticky="ew", padx=12, pady=(10, 4))
        ctk.CTkLabel(h, text="🧮 UltraCalc", font=ctk.CTkFont(size=24, weight="bold")).pack(side="left")
        self.theme_sw = ctk.CTkSwitch(h, text="Light mode", command=self._toggle_theme)
        self.theme_sw.pack(side="right", padx=(12, 0))
        self.sci_sw = ctk.CTkSwitch(h, text="Scientific", command=self._toggle_sci)
        self.sci_sw.select()
        self.sci_sw.pack(side="right", padx=12)
        self.angle = ctk.CTkSegmentedButton(h, values=["DEG", "RAD"], command=self._set_angle)
        self.angle.set("DEG")
        self.angle.pack(side="right", padx=12)

    def _toggle_theme(self):
        ctk.set_appearance_mode("light" if self.theme_sw.get() else "dark")
        self.after(150, self.plot)

    def _toggle_sci(self):
        if self.sci_sw.get():
            self.sci_frame.grid()
        else:
            self.sci_frame.grid_remove()

    def _set_angle(self, v):
        self.engine.deg = v == "DEG"
        self.on_change()

    # ================= calculator tab ====================================== #
    def _build_calc_tab(self):
        t = self.tabs.tab("Calculator")
        t.grid_columnconfigure(0, weight=1)

        self.entry = ctk.CTkEntry(t, height=58, justify="right", font=ctk.CTkFont(family=MONO, size=26))
        self.entry.grid(row=0, column=0, sticky="ew", padx=8, pady=(8, 2))
        self._entry_border = self.entry.cget("border_color")
        self.entry.bind("<Return>", self.calculate)
        self.entry.bind("<KP_Enter>", self.calculate)
        self.entry.bind("<Escape>", lambda e: self.clear())
        self.entry.bind("<Up>", lambda e: self._hist_nav(-1))
        self.entry.bind("<Down>", lambda e: self._hist_nav(1))
        self.entry.bind("<KeyRelease>", self._on_key)

        ctk.CTkLabel(
            t, text_color=MUTED, anchor="e", font=ctk.CTkFont(size=12),
            text="Try:  5!  ·  2^10  ·  sin(30)  ·  20% · 3pi  ·  x := 7  ·  "
                 "1+1=11 (validate!)  ·  ↑↓ history  ·  Enter to evaluate",
        ).grid(row=1, column=0, sticky="ew", padx=10)

        self.result = ctk.CTkLabel(t, text="0", anchor="e", text_color=TEXT,
                                   font=ctk.CTkFont(family=MONO, size=42, weight="bold"))
        self.result.grid(row=2, column=0, sticky="ew", padx=12, pady=(6, 0))
        self.detail = ctk.CTkLabel(t, text="", anchor="e", text_color=MUTED, wraplength=700,
                                   font=ctk.CTkFont(family=MONO, size=13))
        self.detail.grid(row=3, column=0, sticky="ew", padx=12)

        bar = ctk.CTkFrame(t, fg_color="transparent")
        bar.grid(row=4, column=0, sticky="ew", padx=8, pady=(4, 2))
        self.mem_label = ctk.CTkLabel(bar, text="M: 0", text_color=MUTED)
        self.mem_label.pack(side="left", padx=4)
        self.var_label = ctk.CTkLabel(bar, text="", text_color=MUTED)
        self.var_label.pack(side="left", padx=12)
        ctk.CTkButton(bar, text="📋 Copy result", width=110, height=26, command=self._copy_result).pack(side="right")

        pad = ctk.CTkFrame(t, fg_color="transparent")
        pad.grid(row=5, column=0, sticky="nsew", padx=4, pady=4)
        pad.grid_columnconfigure(0, weight=1)
        t.grid_rowconfigure(5, weight=1)

        # memory row
        mem = ctk.CTkFrame(pad, fg_color="transparent")
        mem.grid(row=0, column=0, sticky="ew")
        mem_buttons = [("MC", self.mem_clear), ("MR", self.mem_recall), ("M+", lambda: self.mem_add(1)),
                       ("M−", lambda: self.mem_add(-1)), ("ANS", lambda: self.insert("ans")),
                       ("≟ check", lambda: self.insert("="))]
        for c, (txt, cmd) in enumerate(mem_buttons):
            self._btn(mem, txt, cmd, 0, c, "mem")

        # scientific block
        self.sci_frame = ctk.CTkFrame(pad, fg_color="transparent")
        self.sci_frame.grid(row=1, column=0, sticky="ew")
        sci = [
            [("sin", "sin("), ("cos", "cos("), ("tan", "tan("), ("asin", "asin("), ("acos", "acos("), ("atan", "atan(")],
            [("log", "log("), ("ln", "ln("), ("√", "sqrt("), ("∛", "cbrt("), ("x²", "^2"), ("xʸ", "^")],
            [("n!", "!"), ("π", "pi"), ("e", "e"), ("nCr", "ncr("), ("nPr", "npr("), ("|x|", "abs(")],
            [("mod", " mod "), ("gcd", "gcd("), ("lcm", "lcm("), ("1/x", None), ("±", None), (",", ",")],
        ]
        for r, row in enumerate(sci):
            for c, (label, ins) in enumerate(row):
                if label == "1/x":
                    cmd = lambda: self.wrap("1/(", ")")
                elif label == "±":
                    cmd = lambda: self.wrap("-(", ")")
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
        for r, row in enumerate(keys):
            for c, (label, kind) in enumerate(row):
                if label == "C":
                    cmd = self.clear
                elif label == "⌫":
                    cmd = self.backspace
                else:
                    cmd = lambda s=label: self.insert(s)
                self._btn(main, label, cmd, r, c, kind)
        self._btn(main, "=", self.calculate, len(keys), 0, "eq", span=4)

    def _btn(self, parent, text, cmd, r, c, kind="num", span=1):
        palette = {
            "num": (("gray78", "gray30"), ("gray68", "gray38"), TEXT),
            "fn": (("gray70", "gray24"), ("gray60", "gray32"), TEXT),
            "mem": (("gray82", "gray20"), ("gray72", "gray28"), TEXT),
            "op": (("#3B8ED0", "#1F6AA5"), ("#2F78B3", "#27507A"), "white"),
            "eq": ((GREEN, "#106A43"), ("#25855D", "#0D5636"), "white"),
            "clr": ((RED, "#A33A36"), ("#C23A3F", "#872F2B"), "white"),
        }
        fg, hv, tc = palette[kind]
        b = ctk.CTkButton(parent, text=text, command=cmd, fg_color=fg, hover_color=hv, text_color=tc,
                          height=44, font=ctk.CTkFont(size=16, weight="bold"))
        b.grid(row=r, column=c, columnspan=span, sticky="nsew", padx=3, pady=3)
        for cc in range(c, c + span):
            parent.grid_columnconfigure(cc, weight=1, uniform="k")
        return b

    # ---- entry helpers ----------------------------------------------------- #
    def insert(self, text):
        if not self.entry.get().strip() and text.strip() in ("+", "−", "×", "÷", "^", "%", "mod", "!", "^2"):
            self.entry.insert(0, "ans")
        self.entry.insert(self.entry.index("insert"), text)
        self.entry.focus_set()
        self.on_change()

    def wrap(self, pre, post):
        txt = self.entry.get().strip()
        if not txt:
            txt = "ans"
        self._set_entry(f"{pre}{txt}{post}")

    def _set_entry(self, text):
        self.entry.delete(0, "end")
        self.entry.insert(0, text)
        self.entry.focus_set()
        self.on_change()

    def backspace(self):
        pos = self.entry.index("insert")
        if pos > 0:
            self.entry.delete(pos - 1, pos)
        self.entry.focus_set()
        self.on_change()

    def clear(self):
        self.entry.delete(0, "end")
        self.hist_idx = None
        self._show("0", TEXT, "")
        self.entry.focus_set()

    def _hist_nav(self, d):
        if not self.history:
            return "break"
        i = len(self.history) if self.hist_idx is None else self.hist_idx
        i += d
        if i >= len(self.history):
            self.hist_idx = None
            self._set_entry("")
            return "break"
        i = max(0, i)
        self.hist_idx = i
        self._set_entry(self.history[i]["expr"])
        return "break"

    # ---- memory ------------------------------------------------------------- #
    def _current_value(self):
        try:
            out = self.engine.process(self.entry.get(), commit=False)
            if out["kind"] in ("value", "assign"):
                return out["value"]
        except CalcError:
            pass
        return self.engine.ans

    def mem_add(self, sign):
        self.engine.memory += sign * self._current_value()
        self._refresh_mem()

    def mem_clear(self):
        self.engine.memory = 0
        self._refresh_mem()

    def mem_recall(self):
        self.insert(fmt(self.engine.memory))

    def _refresh_mem(self):
        self.mem_label.configure(text=f"M: {fmt(self.engine.memory)}")

    # ---- evaluating ---------------------------------------------------------- #
    def _show(self, text, color, detail=""):
        self.result.configure(text=text, text_color=color)
        self.detail.configure(text=detail)

    def _describe(self, out, preview=False):
        """Return (text, color, detail) for an engine outcome."""
        dim = MUTED if preview else TEXT
        if out["kind"] == "value":
            return fmt(out["value"]), dim, insights(out["value"])
        if out["kind"] == "assign":
            note = "will be stored as a variable" if preview else "variable stored"
            return f"{out['name']} = {fmt(out['value'])}", dim, note
        vals, ops = out["values"], out["ops"]
        chain = fmt(vals[0])
        for op, v in zip(ops, vals[1:]):
            chain += f" {op} {fmt(v)}"
        if out["ok"]:
            return "✔ Correct", GREEN, f"Checked: {chain}"
        detail = f"Evaluated: {chain}"
        if len(ops) == 1 and ops[0] in ("=", "=="):
            detail += f"   ·   {out['exprs'][0].strip()} is actually {fmt(vals[0])}"
        return "✘ Wrong", RED, detail

    def on_change(self):
        raw = self.entry.get()
        if not raw.strip():
            self._show("0", TEXT, "")
            return
        text = raw + ")" * max(0, raw.count("(") - raw.count(")"))
        try:
            out = self.engine.process(text, commit=False)
        except CalcError:
            self.detail.configure(text="")
            return
        except Exception:
            return
        t, c, d = self._describe(out, preview=True)
        self._show(t, c, d)

    def _on_key(self, e):
        if e.keysym in ("Return", "KP_Enter", "Up", "Down", "Left", "Right", "Escape",
                        "Shift_L", "Shift_R", "Control_L", "Control_R", "Alt_L", "Alt_R"):
            return
        self.hist_idx = None
        self.on_change()

    def calculate(self, event=None):
        raw = self.entry.get().strip()
        if not raw:
            return "break"
        self.hist_idx = None
        try:
            out = self.engine.process(raw)
        except CalcError as ex:
            self._show("Error", RED, str(ex))
            self._flash(RED)
            return "break"
        except Exception as ex:  # never crash the UI
            self._show("Error", RED, f"Unexpected problem: {ex}")
            return "break"

        text, color, detail = self._describe(out)
        self._show(text, color, detail)
        if out["kind"] == "value":
            self.engine.ans = out["value"]
            self.last_text = text
            self._flash(None)
        elif out["kind"] == "assign":
            self.last_text = fmt(out["value"])
            self._flash(None)
        else:
            self.last_text = text
            self._flash(GREEN if out["ok"] else RED)
        self._add_history(raw, text)
        self._refresh_vars()
        return "break"

    def _flash(self, color):
        if color:
            self.entry.configure(border_color=color)
            self.after(900, lambda: self.entry.configure(border_color=self._entry_border))

    def _refresh_vars(self):
        if self.engine.vars:
            self.var_label.configure(text="vars: " + ", ".join(f"{k}={fmt(v)}" for k, v in list(self.engine.vars.items())[:6]))
        else:
            self.var_label.configure(text="")

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
        ctk.CTkButton(row, text="Clear", width=70, fg_color=(RED, "#A33A36"), hover_color=("#C23A3F", "#872F2B"),
                      command=self._clear_history).pack(side="left", padx=2)
        ctk.CTkButton(row, text="Export .txt", command=self._export_history).pack(side="right", padx=2, fill="x", expand=True)

    def _add_history(self, expr, result):
        self.history.append({"expr": expr, "result": result, "t": datetime.now().strftime("%Y-%m-%d %H:%M:%S")})
        self.history = self.history[-200:]
        self._render_history()

    def _render_history(self):
        for w in self.hist_frame.winfo_children():
            w.destroy()
        for item in reversed(self.history[-60:]):
            e = item["expr"] if len(item["expr"]) <= 30 else item["expr"][:28] + "…"
            b = ctk.CTkButton(self.hist_frame, text=f"{e}\n= {item['result']}", anchor="w", height=46,
                              fg_color="transparent", hover_color=("gray85", "gray25"), text_color=TEXT,
                              command=lambda x=item["expr"]: self._set_entry(x))
            b.pack(fill="x", pady=1)
            for seq in ("<Button-2>", "<Button-3>"):
                b.bind(seq, lambda ev, r=item["result"]: self._copy(r))

    def _clear_history(self):
        self.history = []
        self._render_history()

    def _export_history(self):
        if not self.history:
            return
        path = filedialog.asksaveasfilename(defaultextension=".txt", initialfile="ultracalc_history.txt",
                                            filetypes=[("Text file", "*.txt")])
        if path:
            with open(path, "w", encoding="utf-8") as f:
                for i in self.history:
                    f.write(f"[{i.get('t', '')}]  {i['expr']}  =>  {i['result']}\n")

    def _load_history(self):
        try:
            with open(HISTORY_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
            if isinstance(data, list):
                self.history = [d for d in data if isinstance(d, dict) and "expr" in d and "result" in d][-200:]
        except Exception:
            self.history = []
        self._render_history()

    def _on_close(self):
        try:
            with open(HISTORY_FILE, "w", encoding="utf-8") as f:
                json.dump(self.history[-200:], f, ensure_ascii=False)
        except Exception:
            pass
        self.destroy()

    # ================= graph tab ============================================ #
    def _build_graph_tab(self):
        t = self.tabs.tab("Graph")
        top = ctk.CTkFrame(t, fg_color="transparent")
        top.pack(fill="x", padx=6, pady=6)
        ctk.CTkLabel(top, text="f(x) =").pack(side="left", padx=(4, 2))
        self.g_f = ctk.CTkEntry(top, width=340)
        self.g_f.insert(0, "sin(x); x^2/10; 0.5*x")
        self.g_f.pack(side="left", padx=4)
        self.g_f.bind("<Return>", lambda e: self.plot())
        self.g_vals = {}
        for name, default in (("xmin", "-10"), ("xmax", "10"), ("ymin", ""), ("ymax", "")):
            ctk.CTkLabel(top, text=name).pack(side="left", padx=(8, 2))
            en = ctk.CTkEntry(top, width=64, placeholder_text="auto" if name[0] == "y" else "")
            if default:
                en.insert(0, default)
            en.pack(side="left")
            en.bind("<Return>", lambda e: self.plot())
            self.g_vals[name] = en
        ctk.CTkButton(top, text="Plot", width=70, command=self.plot).pack(side="left", padx=8)
        presets = {"Presets": None, "Waves": "sin(x); cos(x)", "Parabolas": "x^2; -x^2+4; 0.2*x^2-3",
                   "Rational": "1/x; 1/(x^2+1)", "Growth": "exp(x/3); ln(x); sqrt(x)",
                   "Bell curve": "exp(-x^2/2)/sqrt(2*pi)", "Cubic": "x^3 - 3*x"}
        self.g_presets = presets
        ctk.CTkOptionMenu(top, values=list(presets), width=110, command=self._preset).pack(side="left")
        self.g_info = ctk.CTkLabel(t, text="Separate several functions with ';'. Hover over the plot to trace the first one.",
                                   text_color=MUTED, anchor="w")
        self.g_info.pack(fill="x", padx=12)
        self.gcanvas = tk.Canvas(t, highlightthickness=0, bd=0)
        self.gcanvas.pack(fill="both", expand=True, padx=8, pady=8)
        self.gcanvas.bind("<Configure>", lambda e: self.plot())
        self.gcanvas.bind("<Motion>", self._trace)
        self.gcanvas.bind("<Leave>", lambda e: self.gcanvas.delete("trace"))

    def _preset(self, name):
        f = self.g_presets.get(name)
        if f:
            self.g_f.delete(0, "end")
            self.g_f.insert(0, f)
            self.plot()

    def plot(self):
        c = self.gcanvas
        w, h = c.winfo_width(), c.winfo_height()
        if w < 80 or h < 80:
            return
        dark = ctk.get_appearance_mode() == "Dark"
        bg, grid, axis, txt = ("#1c1c1c", "#2d2d2d", "#9a9a9a", "#aaaaaa") if dark else ("#ffffff", "#e6e6e6", "#555555", "#555555")
        c.configure(bg=bg)
        c.delete("all")
        self._pl = None
        try:
            xmin = float(self.engine.evaluate(self.g_vals["xmin"].get() or "-10"))
            xmax = float(self.engine.evaluate(self.g_vals["xmax"].get() or "10"))
            if xmax <= xmin:
                raise CalcError("xmax must be bigger than xmin")
            srcs = [re.sub(r"^\s*(?:y|f\(x\))\s*=\s*", "", s) for s in self.g_f.get().split(";") if s.strip()]
            trees = [self.engine.compile(s) for s in srcs][:5]
        except CalcError as ex:
            c.create_text(w / 2, h / 2, text=f"⚠ {ex}", fill=RED, font=(MONO, 14))
            return

        n = min(w, 900)
        xs = [xmin + (xmax - xmin) * i / (n - 1) for i in range(n)]
        series = []
        for tree in trees:
            ys = []
            for x in xs:
                try:
                    y = self.engine.eval_tree(tree, {"x": x})
                    ys.append(float(y))
                except Exception:
                    ys.append(None)
            series.append(ys)

        yfix = []
        for k in ("ymin", "ymax"):
            try:
                yfix.append(float(self.engine.evaluate(self.g_vals[k].get())) if self.g_vals[k].get().strip() else None)
            except CalcError:
                yfix.append(None)
        if None not in yfix and yfix[1] > yfix[0]:
            ymin, ymax = yfix
        else:
            allv = sorted(v for s in series for v in s if v is not None)
            if allv:
                lo, hi = allv[int(0.02 * (len(allv) - 1))], allv[int(0.98 * (len(allv) - 1))]
            else:
                lo, hi = -1, 1
            if hi - lo < 1e-9:
                lo, hi = lo - 1, hi + 1
            pad = (hi - lo) * 0.08
            ymin, ymax = lo - pad, hi + pad

        def px(x):
            return (x - xmin) / (xmax - xmin) * w

        def py(y):
            return h - (y - ymin) / (ymax - ymin) * h

        sx, sy = nice_step(xmax - xmin), nice_step(ymax - ymin, 6)
        v = math.ceil(xmin / sx) * sx
        while v <= xmax:
            c.create_line(px(v), 0, px(v), h, fill=grid)
            c.create_text(px(v) + 3, min(max(py(0), 12), h - 10) + 8, text=f"{v:g}", fill=txt, anchor="w", font=(MONO, 9))
            v += sx
        v = math.ceil(ymin / sy) * sy
        while v <= ymax:
            c.create_line(0, py(v), w, py(v), fill=grid)
            c.create_text(min(max(px(0), 4), w - 40) + 4, py(v) - 8, text=f"{v:g}", fill=txt, anchor="w", font=(MONO, 9))
            v += sy
        if ymin < 0 < ymax:
            c.create_line(0, py(0), w, py(0), fill=axis, width=2)
        if xmin < 0 < xmax:
            c.create_line(px(0), 0, px(0), h, fill=axis, width=2)

        span = ymax - ymin
        for idx, ys in enumerate(series):
            pts, prev = [], None
            color = GRAPH_COLORS[idx % len(GRAPH_COLORS)]

            def flush():
                if len(pts) >= 4:
                    c.create_line(*pts, fill=color, width=2)
                pts.clear()

            for x, y in zip(xs, ys):
                if y is None or abs(py(y)) > 20000 or (prev is not None and abs(y - prev) > span * 3):
                    flush()
                    prev = None if y is None else y
                    continue
                pts += [px(x), py(y)]
                prev = y
            flush()
            c.create_text(10, 12 + idx * 16, text=f"■ {srcs[idx]}", fill=color, anchor="w", font=(MONO, 10, "bold"))

        self._pl = dict(xmin=xmin, xmax=xmax, ymin=ymin, ymax=ymax, w=w, h=h, trees=trees)

    def _trace(self, ev):
        st = self._pl
        c = self.gcanvas
        c.delete("trace")
        if not st or not st["trees"]:
            return
        x = st["xmin"] + ev.x / st["w"] * (st["xmax"] - st["xmin"])
        c.create_line(ev.x, 0, ev.x, st["h"], fill="#888888", dash=(3, 3), tags="trace")
        try:
            y = float(self.engine.eval_tree(st["trees"][0], {"x": x}))
        except Exception:
            y = None
        label = f"x = {x:.4g}" + (f"   y = {y:.4g}" if y is not None else "   y undefined")
        if y is not None:
            yy = st["h"] - (y - st["ymin"]) / (st["ymax"] - st["ymin"]) * st["h"]
            c.create_oval(ev.x - 4, yy - 4, ev.x + 4, yy + 4, fill="#FFD43B", outline="", tags="trace")
        c.create_text(st["w"] - 10, 14, text=label, anchor="e", fill="#FFD43B", font=(MONO, 12, "bold"), tags="trace")

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

    def _build_tools_tab(self):
        sc = ctk.CTkScrollableFrame(self.tabs.tab("Tools"), fg_color="transparent")
        sc.pack(fill="both", expand=True)

        # --- base converter
        card = self._card(sc, "🔢 Base converter")
        r = self._row(card)
        self.base_in = ctk.CTkEntry(r, width=240, placeholder_text="e.g. 255, ff, 1010")
        self.base_in.pack(side="left", padx=4)
        self.base_in.bind("<KeyRelease>", lambda e: self._convert_base())
        self.base_from = ctk.CTkOptionMenu(r, values=["Decimal (10)", "Binary (2)", "Octal (8)", "Hex (16)"],
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
        self.unit_cat = ctk.CTkOptionMenu(r, values=list(UNITS), width=130, command=self._unit_category)
        self.unit_cat.pack(side="left", padx=4)
        self.unit_from = ctk.CTkOptionMenu(r, values=list(UNITS["Length"]), width=100, command=self._convert_unit)
        self.unit_from.pack(side="left", padx=4)
        ctk.CTkLabel(r, text="→").pack(side="left")
        self.unit_to = ctk.CTkOptionMenu(r, values=list(UNITS["Length"]), width=100, command=self._convert_unit)
        self.unit_to.pack(side="left", padx=4)
        ctk.CTkButton(r, text="⇄", width=36, command=self._swap_units).pack(side="left", padx=4)
        self.unit_out = self._out_label(card)
        self._unit_category("Length")

        # --- number lab
        card = self._card(sc, "🔬 Number lab")
        r = self._row(card)
        self.nl_in = ctk.CTkEntry(r, width=240, placeholder_text="a whole number, e.g. 360360")
        self.nl_in.pack(side="left", padx=4)
        self.nl_in.bind("<Return>", lambda e: self._number_lab())
        ctk.CTkButton(r, text="Analyze", width=90, command=self._number_lab).pack(side="left", padx=4)
        self.nl_out = self._out_label(card)

        # --- statistics
        card = self._card(sc, "📊 Statistics")
        r = self._row(card)
        self.st_in = ctk.CTkEntry(r, width=420, placeholder_text="numbers separated by commas: 4, 8, 15, 16, 23, 42")
        self.st_in.pack(side="left", padx=4)
        self.st_in.bind("<Return>", lambda e: self._stats())
        ctk.CTkButton(r, text="Compute", width=90, command=self._stats).pack(side="left", padx=4)
        self.st_out = self._out_label(card)

        # --- calculus lab
        card = self._card(sc, "∫ Calculus lab  (numeric derivative · integral · root)")
        r = self._row(card)
        ctk.CTkLabel(r, text="f(x) =").pack(side="left", padx=(4, 2))
        self.cal_f = ctk.CTkEntry(r, width=240)
        self.cal_f.insert(0, "x^3 - 2*x - 5")
        self.cal_f.pack(side="left", padx=4)
        ctk.CTkLabel(r, text="a").pack(side="left", padx=(8, 2))
        self.cal_a = ctk.CTkEntry(r, width=70)
        self.cal_a.insert(0, "2")
        self.cal_a.pack(side="left")
        ctk.CTkLabel(r, text="b").pack(side="left", padx=(8, 2))
        self.cal_b = ctk.CTkEntry(r, width=70)
        self.cal_b.insert(0, "3")
        self.cal_b.pack(side="left")
        r2 = self._row(card)
        ctk.CTkButton(r2, text="f'(a)", width=90, command=lambda: self._calculus("d")).pack(side="left", padx=4)
        ctk.CTkButton(r2, text="∫ a → b", width=90, command=lambda: self._calculus("i")).pack(side="left", padx=4)
        ctk.CTkButton(r2, text="Find root", width=90, command=lambda: self._calculus("r")).pack(side="left", padx=4)
        self.cal_out = self._out_label(card)

    # ---- base converter
    def _convert_base(self):
        text = self.base_in.get().strip().replace("_", "").replace(" ", "")
        if not text:
            self.base_out.configure(text="", text_color=TEXT)
            return
        base = int(re.search(r"\((\d+)\)", self.base_from.get()).group(1))
        try:
            n = int(text, base)
        except ValueError:
            self.base_out.configure(text=f"'{text}' is not a valid base-{base} number", text_color=RED)
            return
        lines = [f"Decimal : {n}", f"Binary  : {bin(n)}", f"Octal   : {oct(n)}", f"Hex     : {hex(n)}"]
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
        except CalcError:
            self.unit_out.configure(text="—", text_color=MUTED)
            return
        if cat == "Temperature":
            c = {"°C": v, "°F": (v - 32) * 5 / 9, "K": v - 273.15}[a]
            out = {"°C": c, "°F": c * 9 / 5 + 32, "K": c + 273.15}[b]
        else:
            out = v * UNITS[cat][a] / UNITS[cat][b]
        self.unit_out.configure(text=f"{fmt(v)} {a}  =  {fmt(out, 10)} {b}", text_color=TEXT)

    # ---- number lab
    def _number_lab(self):
        try:
            n = _as_int(self.engine.evaluate(self.nl_in.get()), "Input")
        except CalcError as ex:
            self.nl_out.configure(text=f"⚠ {ex}", text_color=RED)
            return
        if abs(n) > 10 ** 13:
            self.nl_out.configure(text="⚠ Please use a number up to 10^13", text_color=RED)
            return
        a = abs(n)
        lines = [f"Number         : {n}", f"Prime?         : {'yes ✨' if is_prime(a) else 'no'}"]
        if a >= 2:
            lines.append(f"Factorization  : {factor_str(factorize(a))}")
            f = factorize(a)
            dcount, dsum = 1, 1
            for p, e in f.items():
                dcount *= e + 1
                dsum *= (p ** (e + 1) - 1) // (p - 1)
            lines += [f"Divisors       : {dcount} (sum {dsum})"]
            lines += [f"Next prime     : {next_prime(a)}"]
            pp = prev_prime(a)
            lines += [f"Previous prime : {pp if pp else '—'}"]
        r = math.isqrt(a)
        lines.append(f"Perfect square : {'yes (' + str(r) + '²)' if r * r == a else 'no'}")
        lines.append(f"Digit sum      : {sum(map(int, str(a)))}")
        lines.append(f"Reversed       : {str(a)[::-1]}")
        lines.append(f"Palindrome     : {'yes' if str(a) == str(a)[::-1] else 'no'}")
        is_fib = any(math.isqrt(x) ** 2 == x for x in (5 * a * a + 4, 5 * a * a - 4) if x >= 0)
        lines.append(f"Fibonacci num  : {'yes' if is_fib else 'no'}")
        self.nl_out.configure(text="\n".join(lines), text_color=TEXT)

    # ---- statistics
    def _stats(self):
        toks = [t for t in re.split(r"[,;\s]+", self.st_in.get().strip()) if t]
        try:
            data = [self.engine.evaluate(t) for t in toks]
            if not data:
                raise CalcError("Enter some numbers first")
        except CalcError as ex:
            self.st_out.configure(text=f"⚠ {ex}", text_color=RED)
            return
        lines = [f"Count     : {len(data)}", f"Sum       : {fmt(sum(data))}",
                 f"Mean      : {fmt(statistics.mean(data))}", f"Median    : {fmt(statistics.median(data))}",
                 f"Mode      : {', '.join(fmt(m) for m in statistics.multimode(data)[:5])}",
                 f"Min / Max : {fmt(min(data))} / {fmt(max(data))}   (range {fmt(max(data) - min(data))})",
                 f"Std dev   : population {fmt(statistics.pstdev(data))}"
                 + (f", sample {fmt(statistics.stdev(data))}" if len(data) > 1 else "")]
        self.st_out.configure(text="\n".join(lines), text_color=TEXT)

    # ---- calculus
    def _calculus(self, mode):
        try:
            src = re.sub(r"^\s*(?:y|f\(x\))\s*=\s*", "", self.cal_f.get())
            tree = self.engine.compile(src)
            f = lambda x: float(self.engine.eval_tree(tree, {"x": x}))
            a = float(self.engine.evaluate(self.cal_a.get() or "0"))
            b = float(self.engine.evaluate(self.cal_b.get() or "1"))
            if mode == "d":
                h = 1e-3
                d = (-f(a + 2 * h) + 8 * f(a + h) - 8 * f(a - h) + f(a - 2 * h)) / (12 * h)
                msg = f"f'({fmt(a)}) ≈ {fmt(round(d, 8))}"
            elif mode == "i":
                n = 2000
                hh = (b - a) / n
                s = f(a) + f(b) + sum((4 if i % 2 else 2) * f(a + i * hh) for i in range(1, n))
                msg = f"∫ from {fmt(a)} to {fmt(b)} of f(x) dx ≈ {fmt(round(s * hh / 3, 8))}"
            else:
                msg = self._find_root(f, a, b)
            self.cal_out.configure(text=msg, text_color=TEXT)
        except CalcError as ex:
            self.cal_out.configure(text=f"⚠ {ex}", text_color=RED)
        except Exception:
            self.cal_out.configure(text="⚠ Could not evaluate f(x) there", text_color=RED)

    @staticmethod
    def _find_root(f, a, b):
        fa, fb = f(a), f(b)
        if fa * fb < 0:  # bisection on [a, b]
            lo, hi = a, b
            for _ in range(200):
                mid = (lo + hi) / 2
                if f(lo) * f(mid) <= 0:
                    hi = mid
                else:
                    lo = mid
            return f"Root in [{fmt(a)}, {fmt(b)}]: x ≈ {fmt(round((lo + hi) / 2, 10))}"
        x = a  # Newton from a
        for _ in range(100):
            h = 1e-6
            d = (f(x + h) - f(x - h)) / (2 * h)
            if d == 0:
                break
            nx = x - f(x) / d
            if abs(nx - x) < 1e-12:
                return f"Root near {fmt(a)} (Newton): x ≈ {fmt(round(nx, 10))}"
            x = nx
        return "No root found - try other starting values (or a bracket where f changes sign)"

    # ================= challenge tab ======================================== #
    def _build_challenge_tab(self):
        t = self.tabs.tab("Challenge")
        self.q = None
        self.score = self.total = self.streak = self.best = 0
        self.times = []

        top = ctk.CTkFrame(t, fg_color="transparent")
        top.pack(fill="x", padx=8, pady=8)
        self.ch_mode = ctk.CTkSegmentedButton(top, values=["Solve it", "Right or Wrong?"], command=lambda _: self._new_question())
        self.ch_mode.set("Right or Wrong?")
        self.ch_mode.pack(side="left", padx=6)
        self.ch_level = ctk.CTkSegmentedButton(top, values=["Easy", "Medium", "Hard"], command=lambda _: self._new_question())
        self.ch_level.set("Easy")
        self.ch_level.pack(side="left", padx=6)
        ctk.CTkButton(top, text="Reset score", width=100, command=self._reset_score).pack(side="right", padx=6)

        self.q_label = ctk.CTkLabel(t, text="", font=ctk.CTkFont(family=MONO, size=38, weight="bold"))
        self.q_label.pack(pady=(50, 20))

        self.solve_box = ctk.CTkFrame(t, fg_color="transparent")
        self.q_entry = ctk.CTkEntry(self.solve_box, width=220, height=46, justify="center",
                                    font=ctk.CTkFont(family=MONO, size=22))
        self.q_entry.pack(side="left", padx=6)
        self.q_entry.bind("<Return>", lambda e: self._answer_solve())
        ctk.CTkButton(self.solve_box, text="Submit", height=46, command=self._answer_solve).pack(side="left", padx=6)

        self.rw_box = ctk.CTkFrame(t, fg_color="transparent")
        ctk.CTkButton(self.rw_box, text="✔  Right", width=180, height=56, font=ctk.CTkFont(size=20, weight="bold"),
                      fg_color=(GREEN, "#106A43"), hover_color=("#25855D", "#0D5636"),
                      command=lambda: self._answer_rw(True)).pack(side="left", padx=12)
        ctk.CTkButton(self.rw_box, text="✘  Wrong", width=180, height=56, font=ctk.CTkFont(size=20, weight="bold"),
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

    def _gen(self, level):
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

    def _new_question(self):
        if self._pending:
            self.after_cancel(self._pending)
            self._pending = None
        expr = self._gen(self.ch_level.get())
        ans = self.quiz_engine.evaluate(expr)
        shown = ans
        if self.ch_mode.get() == "Right or Wrong?":
            if random.random() < 0.5:
                delta = random.choice([-10, -3, -2, -1, 1, 2, 3, 10])
                shown = ans + delta if isinstance(ans, int) else round(ans + delta, 2)
            self.solve_box.pack_forget()
            self.rw_box.pack(after=self.q_label)
            text = f"{expr.replace('*', '×').replace('/', '÷')} = {fmt(shown)}"
            truth = self.quiz_engine.process(f"{expr} = {shown}")["ok"]  # the validator is the referee
        else:
            self.rw_box.pack_forget()
            self.solve_box.pack(after=self.q_label)
            text = expr.replace('*', '×').replace('/', '÷') + " = ?"
            truth = None
            self.q_entry.delete(0, "end")
            self.q_entry.focus_set()
        self.q = {"expr": expr, "answer": ans, "truth": truth, "t0": time.time(), "done": False}
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
        self.times.append(time.time() - self.q["t0"])
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


if __name__ == "__main__":
    ctk.set_appearance_mode("dark")
    ctk.set_default_color_theme("blue")
    UltraCalc().mainloop()
