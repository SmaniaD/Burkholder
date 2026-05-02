#!/usr/bin/env python3
"""Render README equation PNGs from LaTeX."""

from __future__ import annotations

import subprocess
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parent
OUT = ROOT / "readme_equations"
COLOR = "3F73DC"
DENSITY = "220"

PREAMBLE = rf"""
\documentclass[preview,border=1pt]{{standalone}}
\usepackage{{amsmath,amssymb,bm}}
\usepackage[x11names]{{xcolor}}
\newcommand{{\R}}{{\mathbb{{R}}}}
\newcommand{{\N}}{{\mathbb{{N}}}}
\newcommand{{\E}}{{\mathbb{{E}}}}
\newcommand{{\F}}{{\mathcal{{F}}}}
\newcommand{{\norm}}[1]{{\left\lVert #1 \right\rVert}}
\definecolor{{ReadmeBlue}}{{HTML}}{{{COLOR}}}
\begin{{document}}
\color{{ReadmeBlue}}\boldmath
"""

EQUATIONS = {
    "eq-01": r"$\displaystyle w_n,f_n : \Omega \to \R.$",
    "eq-02": r"$\displaystyle f_n \in L^p(\mu) \qquad \text{for every } n\in\N.$",
    "eq-03": r"$\displaystyle |w_n(\omega)| \le 1 \qquad \text{for every } n\in\N \text{ and for } \mu\text{-a.e. } \omega.$",
    "eq-04": r"$\displaystyle \norm{(w\star_m f)_n}_{L^p(\mu)} \le \bigl(p^\ast-1\bigr)\norm{f_n}_{L^p(\mu)},$",
    "eq-05": r"$\displaystyle v(p,x,y) = \left|\frac{x+y}{2}\right|^p - |p^\ast-1|^p \left|\frac{x-y}{2}\right|^p.$",
    "eq-06": r"$\displaystyle u,\ \frac{\partial u}{\partial x},\ \frac{\partial u}{\partial y} : \mathbb{R}\to\mathbb{R}$",
    "eq-07": r"$\displaystyle (x,y)\mapsto u(x,y),\qquad (x,y)\mapsto \frac{\partial u}{\partial x}(x,y),\qquad (x,y)\mapsto \frac{\partial u}{\partial y}(x,y)$",
    "eq-08": r"$\displaystyle |u(x,y)| \le C\bigl(|x|^p+|y|^p\bigr),$",
    "eq-09": r"$\displaystyle \left|\frac{\partial u}{\partial x}(x,y)\right| \le C\bigl(|x|^{p-1}+|y|^{p-1}\bigr),$",
    "eq-10": r"$\displaystyle \left|\frac{\partial u}{\partial y}(x,y)\right| \le C\bigl(|x|^{p-1}+|y|^{p-1}\bigr),$",
    "eq-11": r"$\displaystyle hk\le 0 \Longrightarrow u(x+h,y+k) \le u(x,y) + \frac{\partial u}{\partial x}(x,y)h + \frac{\partial u}{\partial y}(x,y)k,$",
    "eq-12": r"$\displaystyle v(p,x,y)\le u(x,y),$",
    "eq-13": r"$\displaystyle xy\le 0 \Longrightarrow u(x,y)\le 0,$",
    "eq-14": r"$\displaystyle p\ne 2,\ xy=0,\ (x,y)\ne(0,0) \Longrightarrow u(x,y)<0.$",
    "eq-15": r"$p\in (1,\infty)$",
    "eq-16": r"$\left(\Omega,\mathcal{A}\right)$",
    "eq-17": r"$\mu$",
    "eq-18": r"$\Omega$",
    "eq-19": r"$\F=(\F_n)_{n\in \mathbb{N}}$",
    "eq-20": r"$\N$",
    "eq-21": r"$f =(f_n)_{n\in \mathbb{N}}$",
    "eq-22": r"$\F$",
    "eq-23": r"$w=(w_n)_{n\in \mathbb{N}}$",
    "eq-24": r"$\F$",
    "eq-25": r"$n\in\N$",
    "eq-26": r"$w\star_m f$",
    "eq-27": r"$f$",
    "eq-28": r"$w$",
    "eq-29": r"$p^\ast =\max \{ p, (p-1)/p\}$",
    "eq-30": r"$v$",
    "eq-31": r"$u$",
    "eq-32": r"$p\in\mathbb{R}$",
    "eq-33": r"$p>1$",
    "eq-34": r"$C\geq 0$",
    "eq-35": r"$\mathbb{R}^2$",
    "eq-36": r"$x,y,h,k\in\mathbb{R}$",
    "eq-37": r"$u$",
    "eq-38": r"$\mathbb{R}^2$",
}


def render(name: str, body: str) -> None:
    with tempfile.TemporaryDirectory(prefix="readme-equation-") as tmp:
        work = Path(tmp)
        tex = work / f"{name}.tex"
        dvi = work / f"{name}.dvi"
        png = OUT / f"{name}.png"
        tex.write_text(f"{PREAMBLE}{body}\n\\end{{document}}\n", encoding="utf-8")
        subprocess.run(
            ["latex", "-interaction=nonstopmode", tex.name],
            cwd=work,
            check=True,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        subprocess.run(
            ["dvipng", "-T", "tight", "-D", DENSITY, "-bg", "Transparent", "-o", str(png), str(dvi)],
            cwd=work,
            check=True,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )


def main() -> None:
    OUT.mkdir(exist_ok=True)
    for name, body in EQUATIONS.items():
        render(name, body)


if __name__ == "__main__":
    main()
