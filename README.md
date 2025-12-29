# Lambda Calculus in Lean 4

A formally verified implementation of the untyped lambda calculus in Lean 4, featuring:

- De Bruijn indexed terms (no variable capture issues)
- Beta and eta reduction with multiple strategies
- Church encodings (booleans, numerals, pairs, lists)
- Recursive functions via Y combinator
- SKI combinator translation
- Interactive REPL
- 95+ verified theorems

## Quick Start

```bash
# Using nix
nix-shell --run "make build"
nix-shell --run "make repl"

# Or directly with lake
lake build
.lake/build/bin/lambdacalc_repl
```

## REPL Usage

```
Lambda Calculus REPL
Type :help for help, :quit to exit

λ> add 2 3
λx. λy. x (x (x (x (x y))))  (= 5)

λ> :trace K I omega
λx. λy. x
→ λy. λx. x

λ> :ski \x. \y. x
(K I) (K I)

λ> factorial 4
λx. λy. x (x (x ... ))  (= 24)
```

### Commands

| Command | Description |
|---------|-------------|
| `<term>` | Evaluate and reduce to normal form |
| `:reduce <term>` | Reduce using call-by-name |
| `:cbv <term>` | Reduce using call-by-value |
| `:step <term>` | Single reduction step |
| `:trace <term>` | Show full reduction trace |
| `:ski <term>` | Convert to SKI combinators |
| `:parse <term>` | Show de Bruijn representation |
| `:type <name>` | Show built-in definition |
| `:list` | List all built-ins |
| `:help` | Show help |
| `:quit` | Exit |

### Built-ins

- **Combinators**: `I K S B C W`
- **Booleans**: `true false and or not if`
- **Arithmetic**: `succ pred add mul exp sub`
- **Comparisons**: `zero? leq eq gt min max`
- **Pairs**: `pair fst snd`
- **Fixed-point**: `Y Z theta`
- **Recursive**: `factorial fib`
- **Lists**: `nil cons null? head tail length append map foldr reverse sum product nth`
- **Divergence**: `omega Omega`
- **Numerals**: `0, 1, 2, ...`

## Module Structure

```
LambdaCalc/
├── Basic.lean    # Core implementation (terms, reduction, encodings)
├── Proofs.lean   # Formal proofs and theorems
├── Tests.lean    # Test suite (95+ theorems)
└── REPL.lean     # Interactive REPL with parser
```

## Features

### Reduction Strategies

- **Call-by-name** (default): Leftmost-outermost reduction
- **Call-by-value**: Only reduce when argument is a value
- **Eta reduction**: `λx. f x → f` when x not free in f
- **Beta-eta reduction**: Combined strategy

### Church Encodings

```lean
-- Booleans
churchTrue  = λx. λy. x
churchFalse = λx. λy. y

-- Numerals
churchZero = λf. λx. x
churchSucc = λn. λf. λx. f (n f x)

-- Arithmetic
churchAdd  = λm. λn. λf. λx. m f (n f x)
churchMult = λm. λn. λf. m (n f)
```

### SKI Combinators

Convert lambda terms to combinatory logic:

```
λx. x       → I
λx. λy. x   → K
λx. λy. y x → S (K (S I)) K
```

## Verified Properties

The `Proofs.lean` module contains formally verified theorems including:

- Structural properties (size, depth)
- Well-formedness predicates
- Shift and substitution lemmas
- Normal form characterization
- Church encoding correctness
- Alpha equivalence properties
- Closed term properties

## License

MIT
