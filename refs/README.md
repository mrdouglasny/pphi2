# Reference manifest

What `pphi2` cites, where to get it, and what it is cited *for*.

**Policy.** Journal scans and full-text transcriptions of copyrighted articles
are **not published from this repository**. They may be kept locally — the
entries below are `.gitignore`d — but the repo tracks only this manifest.
Obtain each item yourself from the linked source.

**Citation rule.** An axiom docstring or `AXIOM_AUDIT.md` entry must cite a
source listed here, with a page, section, or theorem number, and must record the
source's *actual hypotheses* rather than a paraphrase. Four axioms in this
project were found false or over-quantified between 2026-07 and 2026-08, and in
every case the citation was checkable only from memory.

## Required, not redistributable — obtain your own copy

These are the two most load-bearing sources in the project and neither may be
committed here.

| Source | Cited for | Where |
|---|---|---|
| Glimm & Jaffe, *Quantum Physics: A Functional Integral Point of View*, 2nd ed., Springer 1987 | ~322 citations. Ch. 6.1 propagators; Ch. 8 Nelson estimate; Ch. 10 chessboard; Ch. 18–19 clustering; Thm 19.3.1 rotation anomaly; Thm 6.2.2 lattice RP | Springer / library |
| Simon, *The P(φ)₂ Euclidean (Quantum) Field Theory*, Princeton 1974 | Ch. I dynamical cutoff; §VIII Griffiths–Simon class — **the source of the 2026-08 sextic error** | Princeton UP / library |
| Reed & Simon, *Methods of Modern Mathematical Physics* I–IV | ~54 citations, functional-analytic background | Academic Press / library |

## Local-only (gitignored)

| File | Item | Source |
|---|---|---|
| `GRS1975.md`, `GRS1975-p2.md` | Full-text transcription of Guerra–Rosen–Simon (1975) | transcribed from JSTOR — do not publish |
| `Guerra-P2EuclideanQuantum-1975.pdf`, `guerra1975.pdf` | Guerra, Rosen & Simon, "The P(φ)₂ Euclidean Quantum Field Theory as Classical Statistical Mechanics", *Ann. Math.* **101** (1975) 111–189 | [JSTOR 1970910](https://www.jstor.org/stable/1970910) |
| `simon1975.pdf` | Simon, "Correlation Inequalities and the Mass Gap in P(φ)₂ II", *Ann. Math.* **101** (1975) 260–267 | JSTOR |
| `jaffe-quantum-theory-relativity-2008.pdf` | Jaffe, "Quantum Theory and Relativity", *Contemp. Math.* **449** (2008) 209–245 | [arthurjaffe.com](https://www.arthurjaffe.com/Assets/pdf/Quantum-Theory_Relativity.pdf) |

## arXiv preprints (tracked)

| File | Item |
|---|---|
| `jaffe-reflection-positivity-1802.07880.pdf` | Jaffe, "Reflection Positivity Then and Now" — [1802.07880](https://arxiv.org/abs/1802.07880) |
| `duch-dybalski-jahandideh-2311.04137/` | Duch, Dybalski & Jahandideh, "Stochastic quantization of two-dimensional P(Φ) QFT" — [2311.04137](https://arxiv.org/abs/2311.04137). §5 a priori bound (Prop 5.3), §6 tightness (Prop 6.1). Basis of the retired `ddj/` tree |
| `summers-1203.3991.pdf` | Summers, "A Perspective on Constructive Quantum Field Theory" — [1203.3991](https://arxiv.org/abs/1203.3991) |
| `simon-2011.12335.pdf` | Simon, "Twelve Tales in Mathematical Physics" — [2011.12335](https://arxiv.org/abs/2011.12335) |
| `aizenman-duminilcopin-1912.07973.pdf` | Aizenman & Duminil-Copin, "Marginal triviality of the scaling limits of critical 4D Ising and φ⁴₄ models" — [1912.07973](https://arxiv.org/abs/1912.07973) |
| `chandra-hairer-1612.08138.pdf` | Chandra & Hairer, "An analytic BPHZ theorem for regularity structures" — [1612.08138](https://arxiv.org/abs/1612.08138) |
| `chandra-etal-2201.03487.pdf` | Chandra, Chevyrev, Hairer & Shen, "Stochastic quantisation of Yang–Mills–Higgs in 3D" — [2201.03487](https://arxiv.org/abs/2201.03487) |
| `barashkov-gubinelli-2112.05562.pdf`, `barashkov-gubinelli-1805.10814/` | Barashkov & Gubinelli, variational method for Euclidean QFT |
| `gubinelli-hofmanova-1810.01700/` | Gubinelli & Hofmanová, "A PDE construction of the Euclidean Φ⁴₃ QFT" — [1810.01700](https://arxiv.org/abs/1810.01700) |
| `gubinelli-2025-lecture-notes.pdf` | Gubinelli, lecture notes on stochastic quantisation |

Redistribution of arXiv PDFs is governed per-paper by the author's chosen
licence; the default arXiv licence grants distribution rights to arXiv, not to
third parties. If this repo should stop tracking these too, add `refs/*.pdf` to
`.gitignore` and move the rows above into the local-only table.

## Known gaps

- **1801.06730** was cited in `docs/constructive-qft-guide.md` as
  Chandra–Chevyrev–Hairer–Shen lecture notes on stochastic quantization. That ID
  is an unrelated paper and the intended reference has not been identified.
- A 2005 Jäkel review of the Osterwalder–Schrader theorem was cited at
  `math-ph/0504049`. No such paper could be located; the citation was removed.

## Provenance note (2026-08-23)

Seven of eleven arXiv citations in `docs/constructive-qft-guide.md` pointed at
unrelated papers, and the PDFs in this directory were faithful downloads of
those wrong IDs — a cs.CR password-recovery paper, a materials-science paper on
nanoindentation, an NLP paper, a hep-ph paper on B decays, and others. Three
were single-digit typos with a real paper nearby; four were citations that do
not correspond to any real paper. All were corrected or flagged. Verify a new
reference by opening it, not by trusting its filename.
