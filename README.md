# Localization Complexity

This repository contains the paper "Localization Complexity: Connecting Maximum Entropy Models and Circuit Complexity" by Samuel Schlesinger and Joshua Grochow.

## Abstract

We introduce the *k*-localization complexity L_k(D) of a probability distribution D, defined as the minimum number of latent variables needed to represent D as the marginal of a *k*-local distribution — one whose probability mass function is the maximum entropy distribution consistent with marginal constraints on at most *k* variables. Drawing on the Hammersley–Clifford factorization theorem and the theory of exponential families, we connect this measure to several notions of circuit complexity via a technique we call *local verification*: because each gate in a bounded fan-in circuit depends on few inputs, its correct operation can be enforced by a single marginal constraint.

## Building

Requires a TeX distribution with `pdflatex` and `biber`:

```
pdflatex main.tex
biber main
pdflatex main.tex
pdflatex main.tex
```
