# PotentialPotato

Potential Potato is a dependantly typed programming language based on [Pie](https://github.com/the-little-typer/pie). It extends [Pie](https://github.com/the-little-typer/pie) with [pattern matching](https://en.wikipedia.org/wiki/Pattern_matching), [recursive functions](https://en.wikipedia.org/wiki/Recursion_(computer_science)), and a universe hierarchy.

# Type checking 
Type checking is done using [bidirection type checking](https://ncatlab.org/nlab/show/bidirectional+typechecking). Bidirectional type checking is a type checking strategy in which an expression `e` can be determined to be of type `E` through a combination of checking and synthesis operations. 

$e \implies E$ means we can sythensize the type $E$ given $e$. 

$e \impliedby E$ means the check that $e$ is of type $E$ is successful.

$\dfrac{\Gamma,x:A \vdash M \Leftarrow B}{\Gamma\vdash (\lambda x.M) \Leftarrow (A\to B)}$ tells us that if $x$ is of type $A$, and the check that $M$ is of type $B$ is successful, then checking that $(\lambda (x) M)$ is a function that takes an $A$ and returns a $B$ will be successful. 

$\dfrac{\Gamma\vdash f \Rightarrow (A\to B) \qquad \Gamma\vdash a \Leftarrow A }{\Gamma \vdash f(a) \Rightarrow B}$ tells us that if $f$ sythesizes to a function that takes an $A$ and returns a $B$, and checking that $a$ is an $A$ is successful, then synthesizing $f$ applied to $a$ gives a $B$. 

# Normalization
Expression normalization in Potential Potato is done using [normalization by evaluation](https://en.wikipedia.org/wiki/Normalisation_by_evaluation). Potential Potato evaluates expressions into meta-level data structures (in our case Racket structures). They can be converted back into Potential Potato syntax using a read-back function. Normalization is done through a combination of evaluation and reading back. For example, to normalize a lambda function, it is evaluated into a `Closure` structure, which contains the body of the function, along with current environment extended with the function's argument. The function can be normalized by reading back:

1. Take the argument that is in the enviromnent `x` and put `λ (x)` on the top.
2. Evaluated the body of the lambda function, then read the body back.

The result is the normalized lambda expression.

# Pattern Matching
```racket
(match E-in E-out e
  [pat_0 result_0]
  [pat_1 result_1]
  ...
  [!else result_else])
```
Returns the first `result_n` where `e` matches with the pattern `pat_n`. Tokens from `e` can be bound within a case using `!`. For example,
```racket
(match ... some-list
  ...
  [(:: !e !es) !es]
  ...)
```
Matches `some-list` to any list of the form `(:: head tail)` and returns the tail.

To ensure program correctness: 
- `e` must be of type `E-in`.
- Every `result_n` must be of type `E-out`.
- An "else" case must exist that always matches.

These restrictions ensure that the type of a match expression can be synthesized and checked, and that the match expression will always evaluate to a defined and predictable expression.

# Recursive Functions
```racket
(define rec-fib
  (the (Pi ((n Nat)) Nat)
    (lambda (n)
      (match Nat Nat n
        [zero zero]
        [(add1 zero) (add1 zero)]
        [(add1 (add1 !n)) (+ (rec-fib !n) (rec-fib (add1 !n)))]
        [!else !else]))))      
```
Is a recursive function that computes the `n`'th member of the Fibonacci sequence. In order to classify as a recursive function:
- The name of the definition must have prefix `rec-`.
- The bottom of the recursive function must be a match expression.
- The expression being matched must be the last argument to the recursive function.

Gauranteeing Termination:
Let `m` be the expression being matched. For every match case, the pattern is a more informative version of `m`. This means a strict sub-expression of the pattern is a strict sub-expression of `m`. Potential Potato restricts the last argument of every recursive call to be a strict sub-expression of the pattern. Hence, the last argument of every recursive call is a strict sub-expression of `m`. Since the last argument of every recursive function is what will be matched, we know that every recursive call is matching an expression that is a strict sub-expression of whatever the parent call was matching. Since every recursive call is matching a strictly smaller expression, and these exists an "else" case that always matches, the recursive function must terminate.

# Type Subsumption
The main rules for type subsumption are:

$\dfrac{\Gamma \vdash n \in \mathbb{Nat} \leadsto n^{\circ}}{\Gamma \vdash (U\ n)\ type \ \leadsto (U\ n^{\circ})}$, which adds the type (U n) where n is a Nat.

$\dfrac{\Gamma \vdash expr \in (U n) \ \leadsto \ expr^{\circ}}{\Gamma \vdash expr \in (U \ (add1 \ n)) \ \leadsto \ expr^{\circ}}$ Which says that $(U \ n)$ is a subtype of $(U \ (add1 \ n))$.

$\dfrac{\Gamma \vdash n \in \mathbb{Nat} \leadsto n^{\circ}}{\Gamma \vdash \ (U \ n) \in (U \ (add1 \ n)) \ \leadsto \ (U \ n^{\circ})}$ This says that the type of $(U \ n) $is a $(U \ (add1 \ n))$ aswell. So its both a subtype and an element of $(U \ (add1 \ n))$.

$\dfrac{\Gamma \vdash expr \in (U n) \ \leadsto \ expr^{\circ}}{\Gamma \vdash \ expr \in (U \ infty) \ \leadsto \ expr^{\circ}}$ Which says that $(U n)$ is a subtype of $(U infty)$. It is also the case that $(U n) \in (U \infty)$.

Functions such as ind-List have also been modified to facilitate for these higher types:


$\frac{ hello \\
world}{45}$

Note: $infty$ is an expressions that is used for checking types and expressions when running code, but it cannot be explicitly used when writing in PotentialPotato.

# Code Base Structure
Logical constructs such as evaluation, synthesis, sugaring/desugaring, etc. can be found in their own racket files. For example, desugaring can be found in `desugar.rkt`.
