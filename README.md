# Potential Potato

[![Language](https://img.shields.io/badge/Language-Racket-blue.svg)](https://racket-lang.org/)

Potential Potato is a dependently typed functional programming language that extends the [Pie language](https://github.com/the-little-typer/pie) with additional features for mathematical proof construction and verification.

## Additional Features
### Type System
- Universe Hierarchy: Infinite hierarchy of type universes (U₀, U₁, U₂, ...)
- Subtype Relations: Subtyping with contravariant/covariant rules

### Pattern Matching and Recursion
- Structural Pattern Matching: Decompose data with wildcard variables (`!x`) and structural patterns
- Termination-Guaranteed Recursion: Recursive functions with structural decreasing arguments
- Proof by Cases: Case analysis through pattern matching

See [Features](https://github.com/mooddood235/PotentialPotato/blob/main/Features.md)

## Architecture

### Core Components

| Module | Responsibility |
|--------|----------------|
| `TypeChecking.rkt` | Bidirectional type checking with synthesis (`synth`) and checking (`check`) |
| `Evaluation.rkt` | Expression evaluation (`val`) and normalization (`read-back-norm`) |
| `EvaluationStructs.rkt` | Meta-level Racket structures for evaluated expressions |
| `UniverseUtils.rkt` | Universe type hierarchy and subtyping relations |
| `PotentialPotato.rkt` | Main entry point with `run` function |

## Language Examples

### Recursive Function Definition
```racket
(define rec-factorial
  (the (Pi ((n Nat)) Nat)
    (lambda (n)
      (match Nat Nat n
        [zero (add1 zero)]
        [(add1 !k) (mult n (rec-factorial !k))]))))
```

### Pattern Matching with Wildcards
```racket
(match (List Nat) Nat my-list
  [nil zero]
  [(:: !head !tail) !head])
```

### Universe Hierarchy
```racket
;; Nat : (U zero)
;; (U zero) : (U (add1 zero))
;; (U (add1 zero)) : (U (add1 (add1 zero)))
(define type-of-types (the (U (add1 zero)) (U zero)))
```

## Getting Started

> Requires [Racket](https://racket-lang.org/) (version 8.0 or higher)

### Installation & Usage
```bash
git clone https://github.com/mooddood235/PotentialPotato.git
cd PotentialPotato
racket PotentialPotato.rkt
```

### Running Your First Program
```racket
;; In PotentialPotato.rkt, modify the run function call:
(run '(the Nat (add1 (add1 zero))))
```

## Further Reading

- [The Little Typer](https://mitpress.mit.edu/9780262536431/the-little-typer/) - Foundational text for understanding dependent types
- [Type Theory and Formal Proof](https://www.cambridge.org/core/books/type-theory-and-formal-proof/0472640AAD34E045C7F140B46A57A67C) - Comprehensive treatment of type theory
