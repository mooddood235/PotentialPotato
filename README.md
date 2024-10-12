# Potential Potato
Potential Potato is a [dependently typed](https://en.wikipedia.org/wiki/Dependent_type) functional programming language based on the
[Pie](https://github.com/the-little-typer/pie) programming language. It extends Pie with recursive functions, pattern matching, and a universe type hierarchy.

# What Makes It Special?
Potential Potato allows you to write mathematical proofs in the form of a computer program. Potential Potato checks whether your proof is correct, 
and can check your proof against user input.

# How Does It Work?
Potential Potato interprets types in computer programs as mathematical claims. For instance, the type signature `A->B` for a function `f` means $A$ implies $B$. 
Complex claims, like those with universal quantifiers, are represented by special types. Potential Potato allows you to prove a claim (represented by a type)
by constructing a value that has that type. This works because the types in Potential Potato exhibit behaviour such that a claim represented by a
type `T` is true if and only if a value can be constructed with type `T`. The result is that a mathematical claim can be proven by constructing
a Potential Potato computer program with a type that represents that mathematical claim.

# Extended Features
Potential Potato extends Pie with 3 main features. For an in-depth explanation of the extended features and how they work in Potential Potato, please see `Features.md`.
## Recursive Functions
Potential Potato allows programs to be constructed using recursive functions with some restrictions. 
This means mathematical claims can be proven with recursive logic.
## Pattern Matching
Potential Potato provides the ability to pattern match values as-well as types. This allows mathematical claims to be proven using proof by cases.
## Universe Type Hierarchy
Potential Potato provides an infinite hierarchy of "Universe" types. Every base type is of type $U_0$ and every $U_n$ is of type $U_{n+1}$.

# How To Get Started
The entry point of the program is the `run` function found in `PotentialPotato.rkt`. It takes as an argument the program you want to run.

# Code Base Structure
- Potential Potato's starting point is `run` which is found in `PotentialPotato.rkt`. `run` calls top level functions in order to type check the entire program, modify the program's context, evaluate and normalize expressions, and print to the screen.
- Type checking functions are found in `TypeChecking.rkt`. 
  - `synth` is the type synthesizer.
  - `check` is the type checker.
- Evaluation and normalization logic is closely related. Hence, both can be found in `Evaluation.rkt`.
  - `val` is the evaluator. 
    - Every expression has its own evaluator that starts with prefix `do-`. For example, ind-Lists's evaluator is called `do-ind-List`. 
    - Given an expression `e`, `val` decides which evaluater should be used on `e`.
  - `read-back-norm` is the normalizer.
  - `read-back-neutral` is the normalizer for neutral expressions. It is closely linked with `read-back-norm`.
- When a Potential Potato expression is evaluated, it is turned into a  meta-level Racket structure. All the structures can be found in `EvaluationStructs.rkt`.
- Utility functions for specific logical constructs can be found in a suitably named file.
  - General utility functions are found in `GeneralUtils.rkt`.

# Where To Learn More
Potential Potato is based on the Pie programming language, which is based on [The Little Typer](https://mitpress.mit.edu/9780262536431/the-little-typer/). If you are interested in learning about
dependant types, and how Potential Potato works under the hood, the book is highly recommended.
