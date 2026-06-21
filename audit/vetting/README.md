# pphi2 — per-axiom vetting records

One file per architectural axiom, format per
[`templates/vetting-entry.md`](https://github.com/math-commons/formalization-assurance/blob/main/templates/vetting-entry.md)
in the assurance hub.

## Status (2026-06-21)

| Rung | Count | Notes |
|---|---|---|
| Vetting record landed | **1 / 19** | example: `asymInteracting_expMoment_volume_uniform.md` |
| Stub (points to existing evidence) | **0 / 19** | TODO |
| Not yet | **18 / 19** | tracked in [`../../planning/INDEX.md`](../../planning/INDEX.md) |

Until each axiom has a record here, [`policy.yml`](policy.yml) stays at **L1**
(warn). Raise to **L2** once all 17 architectural axioms (and ideally the 2
private scaffolding axioms) have a record.

## Where the vetting evidence lives today

Vetting evidence for pphi2's axioms is currently scattered across:

- [`../../AXIOM_AUDIT.md`](../../AXIOM_AUDIT.md) — dated-entries narrative log
  (newest first); records gemini deep-think verdicts, codex cross-checks,
  literature citations, and discharge-plan revisions.
- [`../../planning/INDEX.md`](../../planning/INDEX.md) — per-axiom status,
  difficulty, dependencies, and link to the live discharge plan.
- [`../../docs/`](../../docs/) — per-axiom discharge plans (many gemini-vetted),
  e.g. `B4B5-design.md` for Layer B2, `asym-expmoment-discharge-via-lee-yang-vet-request.md`
  for Layer A, `cyl-1a-bridge-plan.md` for the Layer C assembly, etc.

The vetting records under this directory are intended to **consolidate**
that evidence into one record per axiom (with verbatim model prompts and
replies), in the hub's reproducible format.

## How to add a record

```bash
cp ~/Documents/GitHub/formalization-assurance/templates/vetting-entry.md \
   audit/vetting/<AxiomName>.md
$EDITOR audit/vetting/<AxiomName>.md
# Then add a `vetting:` row to AXIOM_AUDIT.md → Sources column.
```

A vetting record can cite a verbatim model prompt + reply (the strongest
form, used for new or strengthened axioms) **or** point to an existing
literature proof (LP code) **or** a previous deep-think vetting captured
in `AXIOM_AUDIT.md` (DT code with a date pointer). See `VETTING.md` in
the hub for the convention.

## Axiom inventory

The 19 real axioms (17 architectural + 2 private scaffolding) are the
target population. For the canonical list with file:line locations see
[`../../formalization.yaml`](../../formalization.yaml) and
[`../../planning/INDEX.md`](../../planning/INDEX.md).
