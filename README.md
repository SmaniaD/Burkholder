# The Burkholder Martingale Transform Inequality in Lean

Daniel Smania  
ICMC-USP, Sao Carlos-SP, Brazil  
<daniel.smania@gmail.com>  
<https://smaniad.github.io/HomePage/>

## Overview

This repository proves the *Burkholder inequality for the real-valued martingale transforms* in the Lean proof assistant, as stated in `MartingaleTransforms.lean` and Figure 1.

![Main theorem](Documentation/maintheorem.png)

That is the **Burkholder inequality for the real-valued martingale transforms** (Burkholder 1985).

**Theorem.** Let \(p\in (1,\infty)\). Let \((\Omega,\mathcal{A})\) be a measurable space, and let \(\mu\) be a finite measure on \(\Omega\). Let \(\mathcal{F}=(\mathcal{F}_n)_{n\in \mathbb{N}}\) be a filtration indexed by \(\mathbb{N}\), and let

\[
  w_n,f_n : \Omega \to \mathbb{R}.
\]

be measurable functions such that \(f=(f_n)_{n\in\mathbb{N}}\) is a discrete martingale with respect to \(\mathcal{F}\). Moreover

\[
  f_n \in L^p(\mu)
  \qquad \text{for every } n\in\mathbb{N}.
\]

Suppose that \(w=(w_n)_{n\in\mathbb{N}}\) is a predictable sequence with respect to \(\mathcal{F}\) with

\[
  |w_n(\omega)| \le 1
  \qquad \text{for every } n\in\mathbb{N}
  \text{ and for } \mu\text{-a.e. } \omega.
\]

Then, for every \(n\in\mathbb{N}\),

\[
  \|(w\star_m f)_n\|_{L^p(\mu)}
    \le
  (p^\ast-1)\|f_n\|_{L^p(\mu)},
\]

where \(w\star_m f\) is the martingale transform of \(f\) with respect to \(w\) and \(p^\ast=\max \{ p, (p-1)/p\}\).

See Banuelos and Davis 2011 for more information on this interesting result.

## The Burkholder Function \(v\)

The proof follows Burkholder 1985. The main step there and the analytic heart of the formalization is to prove that the function

\[
  v(p,x,y)
    =
      \left|\frac{x+y}{2}\right|^p
      -
      |p^\ast-1|^p
      \left|\frac{x-y}{2}\right|^p.
\]

has a majorant \(u\) satisfying the theorem in Figure 2 and as stated in `Majorant.lean`. That is,

![Majorant theorem](Documentation/majorant.png)

**Theorem** (Burkholder 1985). Let \(p\in\mathbb{R}\) with \(p>1\). Then there exist

\[
  u,\ \frac{\partial u}{\partial x},\ \frac{\partial u}{\partial y}
    : \mathbb{R}\to\mathbb{R}
\]

and a constant \(C\geq 0\) such that:

A. The functions

\[
  (x,y)\mapsto u(x,y),\qquad
  (x,y)\mapsto \frac{\partial u}{\partial x}(x,y),\qquad
  (x,y)\mapsto \frac{\partial u}{\partial y}(x,y)
\]

are continuous on \(\mathbb{R}^2\).

B. For all \(x,y,h,k\in\mathbb{R}\),

\[
  |u(x,y)| \le C\bigl(|x|^p+|y|^p\bigr),
\]

\[
  \left|\frac{\partial u}{\partial x}(x,y)\right|
    \le C\bigl(|x|^{p-1}+|y|^{p-1}\bigr),
\]

\[
  \left|\frac{\partial u}{\partial y}(x,y)\right|
    \le C\bigl(|x|^{p-1}+|y|^{p-1}\bigr).
\]

C. We have

\[
  hk\le 0
  \Longrightarrow
  u(x+h,y+k)
    \le
  u(x,y)
    + \frac{\partial u}{\partial x}(x,y)h
    + \frac{\partial u}{\partial y}(x,y)k.
\]

D. We have

\[
  v(p,x,y)\le u(x,y).
\]

E. We have

\[
  xy\le 0 \Longrightarrow u(x,y)\le 0.
\]

F. We have

\[
  p\ne 2,\ xy=0,\ (x,y)\ne(0,0)
  \Longrightarrow
  u(x,y)<0.
\]

## An Informal Report On How The Formalization Was Done

The proof of Theorem 2 is particularly painful to formalize in Lean. The function \(u\) is given explicitly in Burkholder 1985, but it is defined piecewise on several sectors of \(\mathbb{R}^2\). Although the argument proving Theorem 2 in Burkholder 1985 occupies only about half a page, is fairly simple, and could be followed by an undergraduate student with a solid background in point-set topology and analysis, a fully manual formalization would probably require several weeks of work, as Codex itself suggested to me, and perhaps even months.

In our case, the formalization became feasible within a manageable amount of time, namely a few days, by using AI tools such as Copilot and Codex in *agent mode*. In practice, we barely had to type any Lean code ourselves; instead, we mostly guided the agent when necessary.

We began by attaching a LaTeX file to Codex containing the main steps of the proof, following Burkholder 1985, and asking it to encode the argument in Lean. This worked reasonably well for the main definitions. We then suggested, in colloquial language, possible strategies for the proof, using classical gluing lemmas from topology and concavity criteria from analysis. Occasionally, we still had to type small pieces of code or provide more precise guidance, especially when the proof required Mathlib-specific formulations.

Agent mode was particularly useful for debugging problems caused by changes in notation or API differences between versions of Mathlib. The cycle of correction, compilation, and further correction became much faster in agent mode, avoiding the repeated copy-paste-compile workflow that was typical of pre-agent AI tools.

Another interesting feature is that ChatGPT has recently started to suggest additional information after answering a question, apparently in an attempt to keep the user engaged. This can be rather annoying in ordinary ChatGPT sessions. However, when coding in Lean with Codex, it is often quite useful, since the model frequently suggests the next natural steps in the formalization.

A particularly annoying feature of Codex is that, after we suggest an approach to a proof, it often replies with something like "that is certainly the natural approach". As a result, it is difficult to know whether Codex really knew how to proceed, or whether it is simply agreeing too readily. At times, it sounds like an overly confident student who does not want to acknowledge that it needs help.

Unfortunately, even with the paid version of Codex, through ChatGPT Plus, together with the Codex extension for Visual Studio Code, we frequently ran out of credits every day. We therefore had to spend additional time purchasing extra credits and restarting sessions in different computing environments.

The result was more than 20,000 lines of Lean code. We believe that this code is unlikely to be optimal; nevertheless, it is remarkable that we barely had to write any proof by hand. Most of the work consisted in guiding the agent using colloquial language and image snapshots from Burkholder 1985. This is quite astonishing when compared with the capabilities of pre-agent AI tools only a few months ago.

## References

Burkholder, D. L. *An elementary proof of an inequality of R. E. A. C. Paley*. Bulletin of the London Mathematical Society 17, 474--478, 1985. DOI: <https://doi.org/10.1112/blms/17.5.474>.
