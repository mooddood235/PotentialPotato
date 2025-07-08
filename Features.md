# Advanced Features of Potential Potato

This document provides a comprehensive technical overview of Potential Potato's extended features beyond the base Pie language. These additions enable mathematical reasoning and proof construction while maintaining type safety and termination guarantees.

## Table of Contents

1. [Pattern Matching](#pattern-matching)
2. [Recursive Functions](#recursive-functions)
3. [Universe Type Hierarchy](#universe-type-hierarchy)
4. [Advanced Subtyping](#advanced-subtyping)

---

## Pattern Matching

### Core Mechanism

```racket
(match type-in type-out expression
  [pattern₀ result₀]
  [pattern₁ result₁]
  ...
  [patternₙ resultₙ])
```

**Semantics**: Given an expression of type `type-in`, return the first `resultᵢ` where the expression matches `patternᵢ`. All results must have type `type-out`.

### Pattern Syntax

#### Literal Patterns
Exact structural matching against normalized expressions:
```racket
;; Matches exactly (add1 zero)
(match Nat Nat n
  [(add1 zero) result]
  ...)
```

#### Wildcard Patterns
Variables prefixed with `!` capture any expression or sub-expression:
```racket
;; !x captures any natural number
(match Nat Nat n
  [(add1 !x) !x]  ; Returns predecessor
  [zero zero])
```

#### Structural Patterns
Complex patterns matching nested structures:
```racket
;; Pattern matching on lists
(match (List Nat) Nat lst
  [nil zero]
  [(:: !head nil) !head]                    ; Single element
  [(:: !h1 (:: !h2 !tail)) (add !h1 !h2)])  ; Multiple elements
```

### Type-Safe Pattern Matching

The type system ensures pattern match exhaustiveness and consistency:

#### Natural Numbers
```racket
<nat-pattern> ::= "zero" | "(add1" <nat-pattern> ")" | "!" <variable>
```

#### Lists
```racket
<list-pattern> ::= "nil" | "(::" <pattern> <list-pattern> ")" | "!" <variable>
```

#### Vectors
```racket
<vec-pattern> ::= "vecnil" | "(vec::" <pattern> <vec-pattern> ")" | "!" <variable>
```

### Formal Type Rules

The pattern matching type rules ensure soundness:

**Wildcard Rule (Else Case)**:

$$\dfrac
{
  \begin{aligned}
    \Gamma &\vdash e \Leftarrow t_{in}\\
    \Gamma, \text{!}p : t_{out} &\vdash r \Leftarrow t_{out}
  \end{aligned}
}
{\Gamma \vdash (\text{match}\ t_{in}\ t_{out}\ e\ [\text{!}p\ r]) \Rightarrow t_{out}}
$$

**Constructor Patterns**:

$$\dfrac
{
  \begin{aligned}
    &\Gamma \vdash e \Leftarrow t_{in}\\
    &\Gamma, t_{in} \equiv (\text{List}\ t_l)\ \textbf{type}, xs : t_{in}, x : t_l \vdash r \Leftarrow t_{out}\\
    &\Gamma \vdash (\text{match}\ t_{in}\ t_{out}\ e\ \text{rest...}) \Rightarrow t_{out}
  \end{aligned}
}
{\Gamma \vdash (\text{match}\ t_{in}\ t_{out}\ e\ [(::\ x\ xs)\ r]\ \text{rest...}) \Rightarrow t_{out}}
$$

---

## Recursive Functions

Recursive functions in Potential Potato enable mathematical induction while guaranteeing termination through structural restrictions.

### Definition Syntax

```racket
(define rec-function-name
  (the (Pi ((parameter type)) return-type)
    (lambda (parameter)
      (match input-type output-type parameter
        [base-case base-result]
        [recursive-case recursive-result]))))
```

### Termination Guarantees

**Structural Decreasing Requirement**: Every recursive call must operate on a strict structural sub-expression of the matched pattern.

#### Example: Factorial Function
```racket
(define rec-factorial
  (the (Pi ((n Nat)) Nat)
    (lambda (n)
      (match Nat Nat n
        [zero (add1 zero)]
        [(add1 !k) (mult n (rec-factorial !k))]))))  ; !k is structurally smaller than (add1 !k)
```

#### Example: List Length
```racket
(define rec-length
  (the (Pi ((lst (List A))) Nat)
    (lambda (lst)
      (match (List A) Nat lst
        [nil zero]
        [(:: !head !tail) (add1 (rec-length !tail))]))))  ; !tail is structurally smaller
```

### Formal Restrictions

1. **Naming Convention**: Function names must be prefixed with `rec-`
2. **Arity Restriction**: Functions must accept exactly one argument
3. **Body Structure**: Function body must be a `match` expression
4. **Argument Matching**: The matched expression must be the function parameter
5. **Structural Decreasing**: All recursive calls must use strict sub-expressions

### Termination Proof Sketch

Given a recursive function with argument `e`:
1. `e` is the expression being matched in the function body
2. Every pattern provides a structural decomposition of `e`
3. Recursive calls use strict sub-expressions of these patterns
4. Therefore, recursive calls operate on strictly smaller structures
5. With finite structural depth and mandatory base cases, termination is guaranteed

---

## Universe Type Hierarchy

The universe hierarchy in Potential Potato provides a predicative type system that avoids paradoxes while enabling higher-order reasoning.

### Hierarchy Structure

```
Types : (U 0) : (U 1) : (U 2) : ... : (U ∞)
```

Where:
- `Nat : (U 0)`
- `(List A) : (U 0)` if `A : (U 0)`
- `(U n) : (U (add1 n))`
- `(U n) : (U ∞)` for any `n`

### Type Formation Rules

**Universe Formation**:
$$\dfrac{\Gamma \vdash n \Leftarrow \text{Nat}}{\Gamma \vdash (U\ n)\ \textbf{type} \leadsto (U\ n^{\circ})}$$

**Universe Membership**:
$$\dfrac{\Gamma \vdash n \Leftarrow \text{Nat}}{\Gamma \vdash (U\ n) \Leftarrow (U\ (\text{add1}\ n)) \leadsto (U\ n^{\circ})}$$

### Practical Applications

#### Type-Level Functions
```racket
;; Function returning types at different universe levels
(define type-elevator
  (the (Pi ((n Nat) (T (U zero))) (U (add1 n)))
    (lambda (level base-type)
      (ind-Nat level
        (lambda (k) (U (add1 k)))
        base-type
        (lambda (pred result) result)))))
```

#### Higher-Order Type Constructors
```racket
;; Generic container type constructor
(define Container
  (the (Pi ((A (U zero))) (U zero))
    (lambda (A)
      (Pair A (List A)))))
```

---

## Advanced Subtyping

Potential Potato implements sophisticated subtyping relations that enable flexible type hierarchies while maintaining soundness.

### Universe Subtyping

**Basic Subtype Relation**:
$$(U\ n) \subset (U\ (\text{add1}\ n))$$

**Implementation**:
```racket
(define universe-subtype?
  (lambda (sub super)
    (match Nat Bool (nat-diff super sub)
      [zero #f]           ; Equal universes
      [(add1 !k) #t])))   ; super is higher level
```

### Function Subtyping

Functions exhibit **contravariant** parameter types and **covariant** return types:

$$\dfrac
{
  \begin{aligned}
    \Gamma &\vdash A \subset D\\
    \Gamma, x:A &\vdash B \subset K
  \end{aligned}
}
{\Gamma \vdash (Pi\ ((x\ A))\ B) \subset (Pi\ ((y\ D))\ K)}$$

#### Example: Higher-Order Function Compatibility
```racket
;; Function expecting (Nat -> (U 2))
(define higher-order-fn
  (the (Pi ((f (Pi ((n Nat)) (U (add1 (add1 zero)))))) (U (add1 (add1 zero))))
    (lambda (f) (f zero))))

;; Function of type (Nat -> (U 1)) - compatible via subtyping
(define compatible-fn
  (the (Pi ((n Nat)) (U (add1 zero)))
    (lambda (n) (U zero))))

;; This application type-checks due to subtyping
(higher-order-fn compatible-fn)
```

### Eliminator Compatibility

Built-in eliminators (`ind-Nat`, `ind-List`, `ind-Vec`) are enhanced to work with universe subtyping:

```racket
;; ind-Nat with higher universe motives
(define proof-with-universes
  (ind-Nat target
    (the (Pi ((n Nat)) (U infinity))  ; Motive at highest universe
      (lambda (n) (U (add1 n))))
    base-case
    step-function))
```

### Subtyping Algorithm

The subtyping checker performs structural comparison:

1. **Universe Comparison**: Direct level comparison
2. **Function Comparison**: Contravariant parameter, covariant return
3. **Constructor Comparison**: Covariant in all type arguments
4. **Neutral Type Handling**: Conservative approximation for undetermined types
