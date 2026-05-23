# Isabelle Formalization of Relational Hyper Hoare Logic

This repository contains the Isabelle/HOL formalization accompanying Matej Martinček's master's thesis, *Relational Hyper Hoare Logic*, submitted as part of the requirements for the Master's degree at ETH Zürich.

The structure of the Isabelle source code closely follows the structure of the thesis itself. In particular, the formalization is divided into theories corresponding to the individual chapters of the thesis. These theories are further subdivided into sections that largely mirror the corresponding sections of the written report. The goal of this organization is to make navigation between the thesis and the mechanized proofs as straightforward as possible.

The theories are therefore organized conceptually rather than purely technically. Definitions, theorems, and proof rules are generally located in the theories and sections in which they are introduced and discussed in the thesis.

The repository is intended to be navigated together with the thesis:
- the thesis provides the intuition, explanations, and high-level proof ideas,
- the Isabelle theories provide the complete mechanized definitions and proofs.

## Note on the HHL directory

The `HHL` directory contains theories not developed as part of the *Relational Hyper Hoare Logic* master's thesis. They were developed for the *Hyper Hoare Logic* paper. These theories are included because Relational Hyper Hoare Logic extends Hyper Hoare Logic and therefore reuses some of its definitions and results.

All theories located at the topmost level of the repository were developed as part of the *Relational Hyper Hoare Logic* master's thesis. 

## Usage note
Any of the theorey files can be opened in Isabelle/jEdit and traversed independently. All other required theories will be loaded automatically.