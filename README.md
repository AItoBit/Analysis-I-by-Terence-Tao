# Analysis I (Terence Tao) — Lean 4 formalizations

Lean 4 / Mathlib formalizations of exercises from Terence Tao's *Analysis I*.
Every proof below is complete — no `sorry`s, no unjustified `axiom`s.

Chapter 2 builds the natural numbers from scratch (a hand-rolled Peano type),
matching how Tao himself develops them in that chapter. From chapter 3 onward,
files build on Mathlib's own number systems (`ℕ`, `ℤ`, `ℚ`, `ℝ`) and analysis
library, restating each definition or exercise in Mathlib's terms before
proving it.

## Building

This repo is a [Lake](https://github.com/leanprover/lake) project.

```sh
lake exe cache get   # download prebuilt Mathlib oleans (fast)
lake build           # typecheck every exercise file
```

A GitHub Actions workflow (`.github/workflows/ci.yml`) runs this on every push
and pull request, and additionally fails the build if any file contains
`sorry`.

## Layout

Each chapter of the book has its own numbered folder. Inside, each exercise
gets its own file, named `TaoExercise<chapter>_<section>_<number>.lean` (a
couple of files cover two closely related exercises together and are named
accordingly). Files do not import each other — each is self-contained,
importing only Mathlib (or, in chapter 2, defining what it needs from
scratch).

## Progress

227 exercises formalized so far, across chapters 2–11 (chapter 1 is the
book's introduction and has no exercises).

| Ch. | Title | Done | Exercises |
|---|---|---|---|
| 2 | Starting at the beginning: the natural numbers | 11 | 2.2.1–2.2.6, 2.3.1–2.3.5 |
| 3 | Set theory | 26 | 3.1.2–3.1.5, 3.1.8–3.1.9, 3.3.1–3.3.7, 3.4.1–3.4.8, 3.4.11, 3.5.1, 3.6.2, 3.6.3, 3.6.7 |
| 4 | Integers and rationals | 21 | 4.1.1–4.1.8, 4.2.1–4.2.6, 4.3.1–4.3.5, 4.4.1–4.4.2 |
| 5 | The real numbers | 22 | 5.1.1–5.2.1 (combined), 5.2.2, 5.3.1–5.3.5, 5.4.1–5.4.2, 5.4.4–5.4.8, 5.5.1–5.5.5, 5.6.1–5.6.3 |
| 6 | Limits of sequences | 30 | 6.1.1–6.1.8, 6.1.9–6.1.10 (combined), 6.2.1–6.2.2, 6.3.1–6.3.4, 6.4.1–6.4.7, 6.5.1–6.5.3, 6.6.1–6.6.5 |
| 7 | Series | 14 | 7.1.1–7.1.5, 7.2.1–7.2.6, 7.3.1–7.3.3 |
| 8 | Infinite sets | 21 | 8.1.2–8.1.9, 8.2.1–8.2.4, 8.3.1, 8.5.2–8.5.5, 8.5.7–8.5.10 |
| 9 | Continuous functions on R | 35 | 9.1.1–9.1.11, 9.1.13–9.1.14, 9.2.1, 9.3.1–9.3.3, 9.4.1–9.4.6, 9.5.1, 9.6.1, 9.7.1–9.7.2, 9.8.1–9.8.3, 9.9.1–9.9.5 |
| 10 | Differentiation of functions | 17 | 10.1.2–10.1.7, 10.2.1–10.2.7, 10.3, 10.3.3–10.3.5 |
| 11 | The Riemann integral | 30 | 11.1.1–11.1.4, 11.2.1–11.2.4, 11.3.1–11.3.5, 11.4.1–11.4.2, 11.5.1–11.5.2, 11.6.1–11.6.4, 11.8.1–11.8.4, 11.9.2, 11.10.1–11.10.4 |

### Known gaps

A handful of exercises are still outstanding within otherwise-covered
chapters, notably: 8.1.1, all of 8.4.x; 9.1.12; all of 11.7.x and 11.9.1; and
scattered exercises in 3.1.x, 3.2.x, 3.6.x, and 5.1.x/6.1.x that were folded
into a neighboring combined file instead of getting their own. This list is
generated from the current file set and may drift — treat it as a starting
point for what to pick up next, not a guarantee.

## License

See [LICENSE](./LICENSE).
