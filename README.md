# Proofs-in-Number-Theory
This is a project that provides a handful of mathematical proofs in number theory using Coq.
## General Information
I decided to create this project because I wanted to find a way to combine my love for Mathematics with my love for Computer Science. As such, I decided to use Coq, an interactive mathematical theorem solver to formulate rigorous proofs for difficult mathematical theorems.
## Setup
The newest version of Coq can be downloaded using the following link.
https://coq.inria.fr/
## Example
```
Theorem P15 : ∀ u : Z, u ∈ unit → u = ± 1.
Proof.
intros.
apply A4P1 in H.
exact H.
Qed.
```
## Contact Information
Contact me at aritrasaha01@gmail.com
