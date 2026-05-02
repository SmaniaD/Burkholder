# The Burkholder Martingale Transform Inequality in Lean

Daniel Smania  
ICMC-USP, Sao Carlos-SP, Brazil  
<daniel.smania@gmail.com>  
<https://smaniad.github.io/HomePage/>

## Overview

This repository proves the *Burkholder inequality for the real-valued martingale transforms* in the Lean proof assistant, as stated in `MartingaleTransforms.lean` and Figure 1.

![Main theorem](Documentation/maintheorem.png)

That is the **Burkholder inequality for the real-valued martingale transforms** (Burkholder 1985).

**Theorem.** Let <img src="Documentation/readme_equations/eq-15.png" alt="inline equation 1">. Let <img src="Documentation/readme_equations/eq-16.png" alt="inline equation 2"> be a measurable space, and let <img src="Documentation/readme_equations/eq-17.png" alt="inline equation 3"> be a finite measure on <img src="Documentation/readme_equations/eq-18.png" alt="inline equation 4">. Let <img src="Documentation/readme_equations/eq-19.png" alt="inline equation 5"> be a filtration indexed by <img src="Documentation/readme_equations/eq-20.png" alt="inline equation 6">, and let

![Equation 1](Documentation/readme_equations/eq-01.png)

be measurable functions such that <img src="Documentation/readme_equations/eq-21.png" alt="inline equation 7"> is a discrete martingale with respect to <img src="Documentation/readme_equations/eq-22.png" alt="inline equation 8">. Moreover

![Equation 2](Documentation/readme_equations/eq-02.png)

Suppose that <img src="Documentation/readme_equations/eq-23.png" alt="inline equation 9"> is a predictable sequence with respect to <img src="Documentation/readme_equations/eq-24.png" alt="inline equation 10"> with

![Equation 3](Documentation/readme_equations/eq-03.png)

Then, for every <img src="Documentation/readme_equations/eq-25.png" alt="inline equation 11">,

![Equation 4](Documentation/readme_equations/eq-04.png)

where <img src="Documentation/readme_equations/eq-26.png" alt="inline equation 12"> is the martingale transform of <img src="Documentation/readme_equations/eq-27.png" alt="inline equation 13"> with respect to <img src="Documentation/readme_equations/eq-28.png" alt="inline equation 14"> and <img src="Documentation/readme_equations/eq-29.png" alt="inline equation 15">.

See Banuelos and Davis 2011 for more information on this interesting result.

## The Burkholder Function <img src="Documentation/readme_equations/eq-30.png" alt="inline equation 16">

The proof follows Burkholder 1985. The main step there and the analytic heart of the formalization is to prove that the function

![Equation 5](Documentation/readme_equations/eq-05.png)

has a majorant <img src="Documentation/readme_equations/eq-31.png" alt="inline equation 17"> satisfying the theorem in Figure 2 and as stated in `Majorant.lean`. That is,

![Majorant theorem](Documentation/majorant.png)

**Theorem** (Burkholder 1985). Let <img src="Documentation/readme_equations/eq-32.png" alt="inline equation 18"> with <img src="Documentation/readme_equations/eq-33.png" alt="inline equation 19">. Then there exist

![Equation 6](Documentation/readme_equations/eq-06.png)

and a constant <img src="Documentation/readme_equations/eq-34.png" alt="inline equation 20"> such that:

A. The functions

![Equation 7](Documentation/readme_equations/eq-07.png)

are continuous on <img src="Documentation/readme_equations/eq-35.png" alt="inline equation 21">.

B. For all <img src="Documentation/readme_equations/eq-36.png" alt="inline equation 22">,

![Equation 8](Documentation/readme_equations/eq-08.png)

![Equation 9](Documentation/readme_equations/eq-09.png)

![Equation 10](Documentation/readme_equations/eq-10.png)

C. We have

![Equation 11](Documentation/readme_equations/eq-11.png)

D. We have

![Equation 12](Documentation/readme_equations/eq-12.png)

E. We have

![Equation 13](Documentation/readme_equations/eq-13.png)

F. We have

![Equation 14](Documentation/readme_equations/eq-14.png)

## An Informal Report On How The Formalization Was Done

The proof of Theorem 2 is particularly painful to formalize in Lean. The function <img src="Documentation/readme_equations/eq-37.png" alt="inline equation 23"> is given explicitly in Burkholder 1985, but it is defined piecewise on several sectors of <img src="Documentation/readme_equations/eq-38.png" alt="inline equation 24">. Although the argument proving Theorem 2 in Burkholder 1985 occupies only about half a page, is fairly simple, and could be followed by an undergraduate student with a solid background in point-set topology and analysis, a fully manual formalization would probably require several weeks of work, as Codex itself suggested to me, and perhaps even months.

In our case, the formalization became feasible within a manageable amount of time, namely a few days, by using AI tools such as Copilot and Codex in *agent mode*. In practice, we barely had to type any Lean code ourselves; instead, we mostly guided the agent when necessary.

We began by attaching a LaTeX file to Codex containing the main steps of the proof, following Burkholder 1985, and asking it to encode the argument in Lean. This worked reasonably well for the main definitions. We then suggested, in colloquial language, possible strategies for the proof, using classical gluing lemmas from topology and concavity criteria from analysis. Occasionally, we still had to type small pieces of code or provide more precise guidance, especially when the proof required Mathlib-specific formulations.

Agent mode was particularly useful for debugging problems caused by changes in notation or API differences between versions of Mathlib. The cycle of correction, compilation, and further correction became much faster in agent mode, avoiding the repeated copy-paste-compile workflow that was typical of pre-agent AI tools.

Another interesting feature is that ChatGPT has recently started to suggest additional information after answering a question, apparently in an attempt to keep the user engaged. This can be rather annoying in ordinary ChatGPT sessions. However, when coding in Lean with Codex, it is often quite useful, since the model frequently suggests the next natural steps in the formalization.

A particularly annoying feature of Codex is that, after we suggest an approach to a proof, it often replies with something like "that is certainly the natural approach". As a result, it is difficult to know whether Codex really knew how to proceed, or whether it is simply agreeing too readily. At times, it sounds like an overly confident student who does not want to acknowledge that it needs help.

Unfortunately, even with the paid version of Codex, through ChatGPT Plus, together with the Codex extension for Visual Studio Code, we frequently ran out of credits every day. We therefore had to spend additional time purchasing extra credits and restarting sessions in different computing environments.

The result was more than 20,000 lines of Lean code. We believe that this code is unlikely to be optimal; nevertheless, it is remarkable that we barely had to write any proof by hand. Most of the work consisted in guiding the agent using colloquial language and image snapshots from Burkholder 1985. This is quite astonishing when compared with the capabilities of pre-agent AI tools only a few months ago.

## References

Burkholder, D. L. *An elementary proof of an inequality of R. E. A. C. Paley*. Bulletin of the London Mathematical Society 17, 474--478, 1985. DOI: <https://doi.org/10.1112/blms/17.5.474>.
