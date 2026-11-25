# Paper 6: A Nonvanishing Phase Eliminant for Exact Finite-Field Chirp Recognition

## Files
- `main.tex` — Submission-ready `amsart` LaTeX manuscript.
- `references.bib` — Clean BibTeX bibliography.
- `verify_chirp_eliminant.py` — Standalone Python 3 (stdlib only) verifier checking the Levinson-predictor determinant against direct Leibniz expansion across $r\in\{1,2,3,4\}$ and $p\in\{2,3,5,7,17\}$, exhaustive exact recognition and dense DFT output across all 625 vectors of $\mathbb{F}_5^4$ plus structured/adversarial controls up to $N=16, r=3$, complete Gauss-row reduction across all phases for $1\le N\le 20$, blocked chirp convolution, and sparse fresh-vector operators.
- `FiniteFieldChirpEliminant.lean` — Zero-dependency Lean 4 formal verifier (core `Init` only, verified in Lean 4.36.0 with zero `sorry` and pure kernel reduction) symbolically proving $f(d)=d(d-1)/2\ge 0$ with zero set $\{0,1\}$, the reversal degree maximum $\binom{r+2}{3}$ for all $r\ge 0$, the exact quadratic phase-cancellation identity, even-length half-phase absorption, the blocked integer-binomial chirp identity, and even-length Gauss shift invariance; plus pure-kernel finite verifications over $\mathbb{F}_2, \mathbb{F}_5, \mathbb{F}_7, \mathbb{F}_{17}$ including exhaustive recognition on all 625 vectors of $\mathbb{F}_5^4$.

## How to Compile PDF
1. Upload `main.tex` and `references.bib` to Overleaf (or compile locally with `latexmk -pdf main.tex`).

## Suggested Submission Metadata
- **arXiv primary / secondary:** `cs.SC` (Symbolic Computation) / `math.NT` (Number Theory)
- **MSC 2020:** Primary `68W30`, `11T71`; Secondary `15B05`, `65T50`, `11L05`
- **Target journals (zero-fee):** *Journal of Symbolic Computation*, *Finite Fields and Their Applications*, *ISSAC*.

## Verify Computations and Lean Proofs
```bash
python3 verify_chirp_eliminant.py
lean FiniteFieldChirpEliminant.lean
```
