# Cambridge combinatorics in Lean

[![.github/workflows/push.yml](https://github.com/YaelDillies/cam-combi/actions/workflows/push.yml/badge.svg)](https://github.com/YaelDillies/cam-combi/actions/workflows/push.yml)
[![Gitpod Ready-to-Code](https://img.shields.io/badge/Gitpod-ready--to--code-blue?logo=gitpod)](https://gitpod.io/#https://github.com/YaelDillies/cam-combi)

This repository aims at formalising the mathematics courses relevant to combinatorics that are lectured in Cambridge, UK.

## What is formalisation?

The purpose of this repository is to *digitise* some mathematical definitions, theorem statements and theorem proofs. Digitisation, or formalisation, is a process where the source material, typically a mathematical textbook or a PDF file is transformed into definitions in a target system consisting of a computer implementation of a logical theory (such as set theory or type theory).

### The source

The definitions, theorems and proofs in this repository are (mostly) taken from six Cambridge courses, as well as a course from ETH Zürich:
* Part IV Connections between Model Theory and Combinatorics, Lent 2019, lectured by Julia Wolf
* Part II Graph Theory, Michaelmas 2022, lectured by Julian Sahasrabudhe
* Part III Combinatorics, Michaelmas 2022 & [Michaelmas 2023](https://github.com/YaelDillies/maths-notes/blob/master/combinatorics.pdf), lectured by Béla Bollobás
* Part III Extremal and Probabilistic Combinatorics, Michaelmas 2023, lectured by Julian Sahasrabudhe
* Part III [Ramsey Theory on Graphs, Michaelmas 2024](https://github.com/YaelDillies/maths-notes/blob/master/ramsey_theory.pdf), lectured by Julian Sahasrabudhe
* Part III [Additive Combinatorics, Lent 2024](https://github.com/YaelDillies/maths-notes/blob/master/additive_combinatorics.pdf), lectured by Julia Wolf
* ETH Math-D [Growth in Groups, Winter 2024](https://sites.google.com/view/simonmachado/teaching), lectured by Simon Machado

### The target

The formal system which we are using as a target is [Lean 4](https://lean-lang.org). Lean is a dependently typed theorem prover and programming language based on the Calculus of Inductive Constructions. It is being developed at the [Lean Focused Research Organization](https://lean-fro.org) by Leonardo de Moura and his team.

Our project is backed by [mathlib](https://leanprover-community.github.io), the major classical maths library written in Lean 4.

## Content

The Lean code is located within the `LeanCamCombi` folder. Within it, one can find:
* One subfolder for each course, containing **formal lecture transcripts** in the files named `Lecture1`, `Lecture2`, etc... and **formal example sheet translations** in the files named `ExampleSheet1`, `ExampleSheet2`, etc... We follow the mathlib philosophy of aiming for the most general result within reach. This means that not all proofs follow the lecture notes, and might instead derive a result proved in the lectures from a general theorem. Those general theorems and prerequisite lemmas are proved in other folders. Read below.
* A `Mathlib` subfolder for the **prerequisites** to be upstreamed to mathlib. Lemmas that belong in an existing mathlib file `Mathlib.X` will be located in `LeanCamCombi.Mathlib.X`. We aim to preserve the property that `LeanCamCombi.Mathlib.X` only imports `Mathlib.X` and files of the form `LeanCamCombi.Mathlib.Y` where `Mathlib.X` (transitively) imports `Mathlib.Y`. Prerequisites that do not belong in any existing mathlib file are placed in subtheory folders. See below.
* One folder for each **theory development**. The formal lecture transcripts only contain what was stated in the lectures, but sometimes it makes sense for a theory to be developed as a whole before being incorporated by the prerequisites or imported in the formal lecture transcripts.
* An `Archive` subfolder for **archived results**. It sometimes happens in mathlib that a long argument gets replaced by a shorter one, with a different proof. When the long argument was proved in a lecture, we salvage it to `LeanCamCombi` for conservation purposes.

### Content under development

The following topics are under active development in LeanCamCombi.

* The Erdős-Rényi model for random graphs, aka binomial random graph
* The Littlewood-Offord problem
* The van den Berg-Kesten-Reimer inequality
* Approximate subgroups
* Model theoretic stability and its relation to additive combinatorics

See the [upstreaming dashboard](https://yaeldillies.github.io/cam-combi/upstreaming) for more information.

### Current content

The following topics are covered in LeanCamCombi and could be upstreamed to Mathlib.

* Kneser's addition theorem
* The Sylvester-Chvatal theorem
* Containment of graphs

See the [upstreaming dashboard](https://yaeldillies.github.io/cam-combi/upstreaming) for more information.

The following topics are archived because they are already covered by mathlib, but nevertheless display interesting proofs:
* The Cauchy-Davenport theorem for `ℤ/pℤ` as a corollary of Kneser's theorem.

### Past content

The following topics have been upstreamed to mathlib and no longer live in LeanCamCombi.

* The Ahlswede-Zhang inequality
* The four functions theorem and related discrete correlation inequalities: FKG inequality, Holley inequality, Daykin inequality, Marica-Schönheim inequality
* The Marica-Schönheim proof of the squarefree special case of Graham's conjecture
* The Cauchy-Davenport theorem for general groups, and also for linearly ordered cancellative semigroup
* The Erdős-Ginzburg-Ziv theorem
* Chevalley's theorem about constructible sets with and without a complexity bound

## Getting the project

To build the Lean files of this project, you need to have a working version of Lean.
See [the installation instructions](https://lean-lang.org/install/).
Alternatively, click on the button below to open an Ona workspace containing the project.

[![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/YaelDillies/cam-combi)

In either case, run `lake exe cache get` and then `lake build` to build the project.

### Contributing

**This project is open to contribution**. You are in fact encouraged to have a look at the example sheet translations and try your hand at one of the problems. If you manage to prove one of them, please open a PR!

If you want to contribute a theorem or theory development, please open a PR! Note however that the standard of code is pretty high and that is not because you have formalised a concept/proved a theorem that it can be included into LeanCamCombi as is. Nonetheless I am willing to review your code and put it in shape for incorporation.
