# Rocq Core: CIC Reduction & Kernel

---

## Proof Checking in Coq Kernel

- Type-check each term: `Γ ⊢ t : T`
- Verify convertibility: `t ≡ u` (using reduction)
- Check guarded fixpoints (termination)
- Validate inductive definitions (strict positivity, universe constraints)

The kernel is ~8-10k LOC of OCaml that performs these checks.

---

## Trusted Computing Base

Coq's kernel (`coq/kernel/`) — the code that checks CIC proofs:

```
coq/kernel/
├── term.ml              ~1,500 LOC  (CIC term representation)
├── typeops.ml           ~1,500 LOC  (type-checking + η comparison)
├── reduction.ml         ~1,500 LOC  (βδιζ reduction)
├── univ.ml              ~2,000 LOC  (universe constraints)
├── inductive.ml         ~1,500 LOC  (inductive type checking)
├── mod_typing.ml        ~1,000 LOC  (module system)
├── declarations.ml        ~500 LOC
└── [retroknowledge, etc] ~500 LOC
```

**Total**: ~8-10k LOC of OCaml

---

## Coq Terms for a JS Dev

Coq terms are like JS expressions where:
1. You can't write infinite loops
   - Mechanical check by Kernel's guard checker
2. Simplifying always gives one answer
   - Proved: Church-Rosser (1936), SN for CIC (Coquand & Huet 1988)

```
t, u ::=                              -- terms
  | Prop, Set, Type(i)             -- sorts (universes)
  | x                              -- variables
  | λx:T. t                        -- lambda abstraction (term level)
  | t u                            -- application
  | ∀x:T, U                        -- Pi type (Πx:T.U) [Coq syntax]
  | Inductive types                  -- e.g., nat, list
  | Constructors                      -- e.g., O, S, nil, cons
  | match/case                      -- elimination
  | fix                            -- guarded fixpoints
```

**Key distinction**:
- `λx:T. t` is a *term* (function expression)
- `Πx:T. U` (written `∀x:T, U` in Coq) is the *type* of such terms

---

## Atomic Proof Steps (CIC Conversion)

The kernel checks `t ≡ u` by reducing both to normal form, then comparing.

**5 reductions** (each is a rewrite rule):

Greek letter mnemonics:
- **β** (beta) = **B**inding — substitute **b**ound variable
- **δ** (delta) = **D**efinition — **d**elta-expand a name
- **ι** (iota) = **I**nductive — eliminate an **i**nductive constructor
- **ζ** (zeta) = **Z**e let — **z**ap the `let` binding
- **η** (eta) = **E**xtensionality — functions equal if they behave the same

---

### 1. β-reduction (beta)
Applying a lambda substitutes the argument into the body.

```
(λx:T. t) u  →β  t[x:=u]
```

**JS translation**:
```
(x => x + 1)(2)  →β  2 + 1
```

**Example**:
```
(λx. x + 1) 2  →β  2 + 1
```

---

### 2. δ-reduction (delta)
A defined name is replaced by its body.

```
f  →δ  t     (when f := t)
```

**Example**:
```
Given: Definition inc := λx. x + 1

inc 2  →δ  (λx. x + 1) 2
```

---

### 3. ι-reduction (iota)
A `match` on a constructor reduces to the corresponding branch.

```
match S n with O ⇒ t1 | S n' ⇒ t2 end  →ι  t2[n:=n']
```

**Example**:
```
match S 2 with O ⇒ 0 | S n' ⇒ n' + 1 end  →ι  2 + 1
```

---

### 4. ζ-reduction (zeta)
A `let` binding substitutes the value into the body.

```
let x := t in u  →ζ  u[x:=t]
```

**Example**:
```
let x := 3 in x + 1  →ζ  3 + 1
```

---

### 5. η-contraction (eta)
Used as a **comparison rule** in `typeops.ml`, not as a term-rewriting reduction.

```
compare(λx. f x, f):
  body = f x? Yes.
  x free in f? No.
  → "EQUAL" (no term gets rewritten)
```

**Example**:
```
λx. plus 2 x  ≡  plus 2     ✓
```

**Not a reduction step** — the kernel does NOT rewrite `λx. f x` to `f`. It recognizes this pattern during structural comparison.

---

## Bug Rate

From POPL 2024 paper *"Correct and Complete Type Checking and Certified Erasure for Coq, in Coq"*:

> "on average, **one critical bug has been found every year** in Coq"

Sources: [critical-bugs.md](https://github.com/coq/coq/blob/master/dev/doc/critical-bugs.md)

| Year | Bug | Fixed in |
|------|-----|----------|
| 2019 | De Bruijn bug in SProp relevance | Coq 8.10.1 |
| 2020 | Incompleteness in cumulative inductives | Coq 8.13+ |
| 2025 | Module aliasing unsoundness | Coq 9.0.1 |

---

## Software Releases

| Release | Year | Notes |
|---------|------|-------|
| **Coq 4.10** | 1989 | First release; Coquand & Huet's first peer-reviewed paper (1986) |
| **Coq 7.0** | ~2001 | First modular ~10k LOC kernel (Filliâtre & Barras redesign) |
| **Coq 8.9.1** | 2019 | OCPL port; **we're using this** (`ocpl-coq-8.9.1`) |
| **Coq 8.14** | 2021 | Completeness bug found by MetaCoq verification |
| **Coq 9.0.1** | 2025 | Latest critical bug fix (module aliasing) |

---

## References

**Church-Rosser (Confluence)**:
- Church, Rosser (1936). "Some properties of conversion". *Transactions of the AMS*.
- Barendregt (1984). *The Lambda Calculus: Its Syntax and Semantics*.

**Strong Normalization (SN) for CIC**:
- Coquand, Huet (1988). "The Calculus of Constructions".
- Paulin-Mohring (1992). "Inductive Definitions in the System Coq".
- Werner (1994). "A normalization proof for the Calculus of Constructions".
- Geuvers (1995). "The Church-Rosser property for CIC".

**Calculus of Constructions (CoC)**:
- Coquand, Huet (1986). "Constructions: A Higher Order Proof System for Mechanizing Mathematics".

**Calculus of Inductive Constructions (CIC)**:
- Paulin-Mohring (1990). "Extracting λ from Coq".
- Werner (1997). "A formalized proof of Strong Normalization for CIC".

**Verified Checker for CIC**:
- Sozeau et al. (2024). "Correct and Complete Type Checking and Certified Erasure for Coq, in Coq". *Journal of the ACM*.
