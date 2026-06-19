# 4-PEL: 4-Valued Probabilistic Epistemic Logic

This repository contains the **Lean 4 formalization** of the 4-Valued Probabilistic Epistemic Logic (4-PEL), as introduced in the paper *"The Cartography of Paradoxes: Unifying Probabilistic Epistemic Logic and Non-Bivalent Validity"*.

4-PEL elegantly resolves major epistemic paradoxes (such as the Liar, Lottery, Preface, and Moore's paradoxes) by embedding a Lockean threshold belief operator into the 4-valued Belnap-Dunn (First Degree Entailment) semantic space. It provides a mathematical mechanism to paraconsistently isolate contradictions and prevent epistemic explosion (*ex falso quodlibet*).

---

## 📖 For Academic Reviewers

This repository provides the **machine-checked mathematical backbone** of the 4-PEL framework. Rather than relying solely on philosophical argumentation, the core mathematical claims of the paper have been strictly verified using the Lean 4 interactive theorem prover.

### What is formalized here?
1. **Belnap-Dunn Logic:** The foundational 4-valued logic consisting of True ($T$), False ($F$), Epistemic Gluts ($B$), and Epistemic Gaps ($N$), along with non-bivalent validity standards (ST and LP).
2. **The 4-PEL Kripke Model:** A rigorous finite-state model featuring accessibility relations and local probability measures ($\mu_{i,w}$).
3. **The Lockean Belief Operator:** A dynamic threshold operator $B_i(\phi)$ that maps probabilities over possible worlds back into the 4-valued FDE algebra.
4. **The Glut Boundary Theorem:** A formal, computationally verified proof of the paper's central theorem: If an agent rationally believes a contradiction, the objective probability of an ontological glut ($P_B$) is mathematically bounded by $P_B \ge 2c - 1$.

Reviewers can browse the source files directly on GitHub to examine the axioms and definitions without needing to install Lean locally.

---

## 💻 For Lean Enthusiasts

Welcome! This project demonstrates how to elegantly formalize a novel epistemic logic in Lean 4. 

### Architecture
- `PEL4/FDE.lean`: Defines the 4-valued algebra and logical connectives.
- `PEL4/Model.lean`: Defines the Kripke structures and finite probability measures.
- `PEL4/Belief.lean`: Implements the threshold probability operator.
- `PEL4/Theorems.lean`: The core mathematical proofs.

### A Note on `Mathlib` and Performance
To keep this project extremely fast to compile and entirely dependency-free, we intentionally chose **not** to import the massive `Mathlib` library (which would be required for continuous measure theory and Rational `linarith` tactics). 

Instead, probability distributions over the finite sets of accessible worlds (Model Checking) are represented using `Int` (e.g., scaled to 100% or permille). This enables the use of Lean 4's lightning-fast built-in presburger arithmetic tactic (`omega`) to close the core proofs in under 500 milliseconds. The geometric and logical rigor of the theorems remains fully isomorphic to a Rational/Real implementation.

### How to Build
To verify the proofs locally, ensure you have [Lean 4 and Lake installed](https://leanprover-community.github.io/get_started.html).

Clone the repository and build:
```bash
git clone https://github.com/cr4bbz/4PEL-Lean-Formalization.git
cd 4PEL-Lean-Formalization
lake build
```
If the command finishes successfully, all theorems have been automatically verified by your machine.