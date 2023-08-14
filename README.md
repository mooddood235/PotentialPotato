# Potential Potato

Potential Potato is a [dependently typed](https://en.wikipedia.org/wiki/Dependent_type) functional programming language based on [Tartlet](https://davidchristiansen.dk/tutorials/nbe/). It extends Tartlet with many of the features in the [Pie](https://github.com/the-little-typer/pie) programming language, aswell as pattern matching, recursive functions, and a universe hierarchy.

# Pattern Matching

Pattern matching is the process of checking whether a given sequence of tokens matches in structure or syntax another sequence of tokens.

Pattern matching is done in Potential Potato through the built-in `match` function.

```racket
(match type-in type-out e
  [pat_0 res_0]
  [pat_1 res_1]
  ...
  [pat_n res_n])
```

Given an expression `e` of type `type-in`, return the first `res_i` where `e` matches with the pattern `pat_i`. Every result is of type `type-out`.

## Pattern Syntax
A pattern can be any Potential Potato expression in normal form. So, `zero`, `(add1 zero)`, and `(:: 'hello nil)` are all valid patterns.

Let a `b-list` refer to any sequence of tokens properly enclosed within brackets. `(hello (world my friend))` is a `b-list`. 

Let `e` be the expression being matched and `pat` be some pattern.

A token in `pat` prefixed with `!` matches with any token or `b-list` in the same spot structurally in `e`.

## Examples

Expression `e = (add1 zero)` matches with pattern `pat = (add1 zero)` because all the tokens in `e` match structuraly and syntactically with all the tokens in `pat`.

Expression `e = (hello there)` does NOT match with pattern `pat = (bye there)` because `pat` expects the token `bye` where `e` has `hello` instead.

Expression `e = (:: big (:: boss nil))` matches with pattern `pat = (:: big (:: !x nil))` because all the tokens match structuraly and syntactically except for `!x`. However, `!x` is prefixed with `!`, which means it matches with whatever is in the same spot in `e`. In this case `!x` in `pat` is matching with `boss` in `e`.

Expression `e = (:: big (:: boss nil))` matches with pattern `pat = (:: big !hi)` because all the tokens match structuraly and syntactically except for `!hi`. However, `!hi` is prefixed with `!`, which means it matches with whatever is in the same spot in `e`. In this case `!hi` in `pat` is matching with the `b-list` `(:: boss nil)` in `e`.

## Grammar

```
<match-expr> ::= "(match" <type-in> <type-out> <expr> <cases> ")"
<cases> ::= <case> | <case> <cases>
<case> ::= "[" <pattern> <result> "]"
<nat> ::= "zero" | "(add1" <nat> ")"
<list> ::= "nil" | "(::" <pattern> <list> ")"
<vec> ::= "vecnil" | "(vec::" <pattern> <vec> ")"
<uni> ::= "(U" <nat> ")"
<pattern> ::= <nat> | <list> | <vec> | <uni> | "!" <literal>
```

## Inference Rules
$\frac
{\Gamma \ \vdash \ e \impliedby t_{in} \ \Gamma, \ \text{!}p \ : \ t_{out}\ \vdash \ r \impliedby t_{out}}
{\Gamma \ \vdash \ (\text{match} \ t_{in} \ t_{out} \ e \ [\text{!}p \ r]) \implies t_{out}}
[SynthElse]
$

$\frac
{\Gamma \ \vdash \ e \impliedby t_{in} \ \Gamma, \ \text{zero} \ : \ \text{Nat} \ \vdash \ r \impliedby t_{out} \ \Gamma \ \vdash (\text{match}\ t_{in} \ t_{out} \ e \ rest...) \implies t_{out}}
{\Gamma \ \vdash \ (\text{match} \ t_{in} \ t_{out} \ e \ [\text{zero} \ r] \ rest...) \implies t_{out}}
[SynthZero]
$

$\frac
{\Gamma \ \vdash \ e \impliedby t_{in} \ \Gamma, \ \text{n} \ : \ \text{Nat} \ \vdash \ r \impliedby t_{out} \ \Gamma \ \vdash (\text{match}\ t_{in} \ t_{out} \ e \ rest...) \implies t_{out}}
{\Gamma \ \vdash \ (\text{match} \ t_{in} \ t_{out} \ e \ [(\text{add1} \ n) \ r] \ rest...) \implies t_{out}}
[SynthAdd1]
$

$\frac
{\Gamma \ \vdash \ e \impliedby t_{in} \ \Gamma, \ \text{nil} \ : \ t_{in} \ \vdash \ r \impliedby t_{out} \ \Gamma \ \vdash (\text{match}\ t_{in} \ t_{out} \ e \ rest...) \implies t_{out}}
{\Gamma \ \vdash \ (\text{match} \ t_{in} \ t_{out} \ e \ [\text{nil} \ r] \ rest...) \implies t_{out}}
[SynthNil]
$

$\frac
{\Gamma \ \vdash \ e \impliedby t_{in} \ \Gamma, \ t_{in} \ : \ (\text{List} \ t_l), \ xs \ : \ t_{in}, \ x \ : \ t_l \ \vdash \ r \impliedby t_{out} \ \Gamma \ \vdash (\text{match}\ t_{in} \ t_{out} \ e \ rest...) \implies t_{out}}
{\Gamma \ \vdash \ (\text{match} \ t_{in} \ t_{out} \ e \ [(:: \ x \ xs)\ r] \ rest...) \implies t_{out}}
[Synth::]
$

$\frac
{\Gamma \ \vdash \ e \impliedby t_{in} \ \Gamma, \ \text{vecnil} \ : \ t_{in} \ \vdash \ r \impliedby t_{out} \ \Gamma \ \vdash (\text{match}\ t_{in} \ t_{out} \ e \ rest...) \implies t_{out}}
{\Gamma \ \vdash \ (\text{match} \ t_{in} \ t_{out} \ e \ [\text{vecnil} \ r] \ rest...) \implies t_{out}}
[SynthNil]
$


$\frac
{\Gamma \ \vdash \ e \impliedby t_{in} \ \Gamma, \ t_{in} \ : \ (\text{Vec} \ t_l \ n), \ xs \ : \ t_{in}, \ x \ : \ t_l \ \vdash \ r \impliedby t_{out} \ \Gamma \ \vdash (\text{match}\ t_{in} \ t_{out} \ e \ rest...) \implies t_{out}}
{\Gamma \ \vdash \ (\text{match} \ t_{in} \ t_{out} \ e \ [(\text{vec::} \ x \ xs)\ r] \ rest...) \implies t_{out}}
[SynthVec::]
$

$\frac
{\Gamma \ \vdash \ e \impliedby t_{in} \ \Gamma, \ \text{n} \ : \ \text{Nat} \ \vdash \ r \impliedby t_{out} \ \Gamma \ \vdash (\text{match}\ t_{in} \ t_{out} \ e \ rest...) \implies t_{out}}
{\Gamma \ \vdash \ (\text{match} \ t_{in} \ t_{out} \ e \ [(\text{U} \ n) \ r] \ rest...) \implies t_{out}}
[SynthU]
$
# Recursive Functions
A function is recursive if its definition contains a call to itself.

## Grammar

```
<recursive-function> ::= "(define rec-" <literal>
                           "(the (Pi ((" <literal> <type> "))" <type> ")"
                            "(lambda (e)"
                              "(match" <type-in> <type-out> "e" <cases> "))))"
<cases> ::= <case> | <case> <cases>
<case> ::= "[" <pattern> <result> "]"
<nat> ::= "zero" | "(add1" <nat> ")"
<list> ::= "nil" | "(::" <pattern> <list> ")"
<vec> ::= "vecnil" | "(vec::" <pattern> <vec> ")"
<uni> ::= "(U" <nat> ")"
<pattern> ::= <nat> | <list> | <vec> | <uni> | "!" <literal>
```

## Restrictions
- A recursive function's name must be prefixed with `rec-`.
- The function must be of one argument.
- The body of the recursive function must be a match expression.
- The expression being matched is the argument to the function.
- Every recursive call's argument must be a strict sub-expression of the pattern.

## Guaranteeing Termination
Let `e` be the argument to a recursive function. According to the restrictions, `e` must be the expression being matched, and every recursive call's argument must be a strict sub-expression of the pattern. Since every pattern is a more informative version of `e`, it follows that every recursive call's argument is gauranteed to be a strict sub-expression of `e`. This means that every recursive call is getting an argument that is strictly smaller than the parent call. Since every match expression contains an "else" case, and arguments are always getting smaller, a recursive function must terminate.
# Universe Hierarchy

`(U zero)` takes the place of $U$ in Pie.
All the types in Pie that were originally a U now become a (U zero). For example on line 207 in TypeChecking.rkt, when synthesizing the expression Nat. Additionally when checking if Nat is a `(U zero)`, a type is first synthesized for Nat (which is a (U zero)) and then its checked if thats a subtype of the type that was passed into the check function which is a (U zero).

The main rules for type subsumption are:

$\dfrac{\Gamma \vdash n \in Nat \leadsto n^{\circ}}{\Gamma \vdash (U \ n)\ type \ \leadsto (U \ n^{\circ})}$, The type $(U \ n)$ is introduced where $n$ is a Nat. This can be seen on line 174 of TypeChecking.rkt, this line is also used in type checking similarly to Nat.

$\dfrac{\Gamma \vdash expr \in (U \ n) \ \leadsto \ expr^{\circ}}{\Gamma \vdash expr \in (U \ (add1 \ n)) \ \leadsto \ expr^{\circ}}$ This indicates that $(U \ n)$ is a subtype of $(U \ (add1 \ n))$, this can be seen in the following [lines](https://github.com/mooddood235/PotentialPotato/blob/2ea22d0c472bc3649f8693f2145b7789587882ac/UniverseUtils.rkt#L9C4-L13C54) . Later on the symbol $\subset$ will be used for subtype.

$\dfrac{\Gamma \vdash n \in Nat \leadsto n^{\circ}}{\Gamma \vdash \ (U \ n) \in (U \ (add1 \ n)) \ \leadsto \ (U \ n^{\circ})}$ This says that $(U \ n)$ typchecks as a $(U \ (add1 \ n))$. So its not only a subtype but also an element of $(U \ (add1 \ n))$.

$\dfrac{\Gamma \vdash expr \in (U \ n) \ \leadsto \ expr^{\circ}}{\Gamma \vdash \ expr \in (U \ infty) \ \leadsto \ expr^{\circ}}$ Which says that $(U \ n)$ is a subtype of $(U \ infty)$. 

A result which also follows from these rules is that $(U \ n) \in (U \ infty)$ for any Nat $n$.

Note: $infty$ is a special Nat that is used for checking types and expressions when running code in the backend, but it should not be used when writing in PotentialPotato.

# More on Subtyping
This subtyping behavior also extends to functions and other similar objects like Pair, 

$\Gamma \vdash (\Pi \ ((m \ D)) \ K) \ type \ \leadsto \ s$

$\Gamma \vdash \ p \in (\Pi \ ((n \ A)) \ B) \ \leadsto \ p^{\circ}$

$\Gamma \vdash A \subset D \ \leadsto \ A^{\circ} $

$\dfrac{\Gamma,a:A ~ m:D \ \vdash B \subset K \leadsto B^{\circ}} {\ p \in (\Pi \ ((m \ D)) \ K) \ \leadsto \ p^{\circ}}$

The above rules specify that for one Pi expression to be a subtype of another, then their argument types and body types both have to be subtypes.

Consider the following code to highlight this point:

```racket
(define fn (the (Pi ((n Nat) (ft (Pi ((t Nat)) (U (add1 (add1 t)))))) (U (add1 (add1 n))))
                (lambda(m s) (s m))))
(define subfunc (the (Pi ((v Nat)) (U (add1 v)))
                     (lambda(g) (U g))))
(fn (add1 zero) subfunc)

```


# Code Base Structure
- Potential Potato's starting point is `run-program` which is found in `PotentialPotato.rkt`. `run-program` calls top level functions in order to type check the entire program, modify the program's context, evaluate and normalize expressions, and print to the screen.
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
