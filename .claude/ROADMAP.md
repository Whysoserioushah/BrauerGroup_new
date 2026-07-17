# BrauerGroup — Project Roadmap, Status & Working Notes

> **What this file is.** The canonical, account-independent record of this project: what has
> been done, what remains, how we work, and every hard-won gotcha. It mirrors (and can fully
> reconstruct) the live roadmap dashboard. **Keep it updated at every checkpoint** — whenever a
> task is marked done on the dashboard, mirror it here.
>
> **For a fresh Claude session/account:** read this file top to bottom before touching Lean.
> The live dashboard Artifact may be tied to an old account; `.claude/brauer-roadmap.html` in
> this folder is a snapshot of its source and can be re-published as a new Artifact if needed.

Last updated: **2026-07-17** (dashboard rev 67, **65/132 tasks done**, build green 8724 jobs).
🏁 Landed 2026-07-15→17: `CyclicAlgebra.mk_eq_one_iff` (split iff norm, first Goal-A
keystone), the whole **4.7 basis arc**, the **4.8 STRUCTURE THEOREM**
(`GoodRep.compareAlgEquiv` + `mk_crossProduct_factorSet` + `mk_congr_cocycle`), **5.4**
(`exists_mk_cyclicAlgebra_eq` — every Br(L/K) class over cyclic L/K is a cyclic algebra),
and the **`CrossProductAlgebra.single` kit + `induction_linear`** (swept repo-wide).
With 5.5b, both halves of level-iso 6.8's algebra side are done.
Phase-5 remainder: only 5.6 ⇐ 4.14a/b and 5.7 ⇐ 4.11a–e.
Open fronts: **4.14a** (inflation I — easier than 4.11, unlocks 5.6/8.2b/B.7), the **4.11
bimodule arc**, or port wave **6.3a**.

---

## 1. The two final goals

- **GOAL A — `Br(K) ≅ ℚ/ℤ` for K a nonarchimedean local field, COHOMOLOGY-FREE.**
  Purely via cyclic algebras + the unramified tower. No group cohomology anywhere on this path.
- **GOAL B — `Br(K) ≅ H²(Gal(K̄/K), K̄ˣ)`.**
  Finite level `Br(L/K) ≃* H²(Gal(L/K), Lˣ)` over an *arbitrary* base field (prime mathlib-PR
  material), then a directed colimit over finite Galois subextensions along inflation —
  **no profinite topology**; a `ContCohomology` upgrade (B.9) is optional, never a blocker.

Everything is rebuilt CLEANLY on the new foundation
(`BrauerGroup/Algebra/BrauerGroup/Basic.lean` + `BaseChange.lean`). Old files are considered
messy; we recover *results*, not proofs, and delete legacy files in waves (Phase X).

### Phase architecture

| Phase | Role |
|---|---|
| 0–3 | Foundation: Br group via `mk`, relative Br, splitting theory, Skolem–Noether, double centralizer, Koethe, `Br(K) = ⋃ Br(L/K)` — **all COMPLETE** |
| 4 | **Shared TRUNK** (cohomology-free crossed products): comparison chain, basis, structure theorem, canonical conjFactors, bimodule multiplicativity, inflation theorem |
| 5 | **Goal A cyclic layer**: cyclic algebras, split-iff-norm, tower, multiplicativity — core done, remainder trunk-gated |
| 6 | Local fields: ℚ_p / Laurent instances, CFT port waves, Frobenius layer, norm surjectivity (wall #3) |
| 7 | Reduced norm valuation ⇒ every division algebra split by unramified K_n |
| 8 | Goal A assembly into `AddCircle (1 : ℚ)` (colimit-free: subgroup-iSup + `iSupLift`) |
| B | Goal B: H² interface, round trips, `Br(L/K) ≃* H²`, colimit, absolute theorem |
| X | Legacy deletion waves + mathlib PR batch |

Declared milestones: 3.12 ✓ · 6.8 · 7.10 · 8.3 · B.5 · B.8.

---

## 2. Status snapshot (2026-07-14)

- Branch `edison/cleanup`, last commit **ba259cd** (2026-07-15, pushed): the full
  4.5-chain + 4.9 + 5.5b batch. Tree clean.
- **Cyclic core COMPLETE**: 5.1 (CyclicAlgebra + uⁿ = a), 5.2 (CPA(1) ≅ End, `mk_one_eq_one`),
  5.3 (power family + `factorSet_powFamily`), 5.5a (coboundary ⟺ norm). **4.5b + 4.5c done** —
  the trunk comparison chain is two steps from closing.
- Phase 5 remainder entirely **trunk-gated**: 5.4⇐4.8c, 5.5b⇐4.5d/e+4.9, 5.6⇐4.14b, 5.7⇐4.11e.
- **Two open fronts**: trunk **4.5d** (factorSet transport along the intertwining iso — one
  `factorSet_unique` application — then 4.5e finale; with 4.9a/b that unlocks 5.5b) or port
  wave **6.3a** (CFT shims).
- Note 2026-07-14: the P2 shim lives at
  **`BrauerGroup/Algebra/BigOperators/GroupWithZero/Action.lean`** (moved out of the
  Mathlib-mirror dir by Edison; imports retargeted).

### Toolchain

- Lean **4.32.0-rc1**, mathlib pin **cef1e7de** (2026-07-06), **new module system**
  (`module`, `public import`, `@[expose] public section`).
- Full build: `lake build` (≈8723 jobs green). Draft files not in the root build by name:
  `lake build BrauerGroup.Path.To.Module`.
- Mathlib oleans: `lake exe cache get` (fast from local cache).
- Root regeneration: `lake exe mk_all --lib BrauerGroup` (preserves the `-- shake: keep-all`
  header). `#min_imports` works appended per-file (build by name, read the info message) and
  emits module-aware `public import` lines.

---

## 3. Working conventions (Edison's standing rules)

- **Granularity rule**: every open dashboard task ≤ ~3 nontrivial Lean steps; if one balloons
  mid-flight, split it on the dashboard before grinding.
- **Detailed plan first**: for each task Edison usually wants the concrete math + Lean plan
  before any code. Edison implements plenty hands-on; Claude fills sorries / adds API on request.
- **Style**: no underscores in variable names; golf to mathlib standard; mathlib naming.
- **Spec-lemma discipline**: never unfold choice-based defs downstream — expose a small spec
  API and use only it (`fromH2_H2π`, `powFamily_val`, `genExp_*` are the models).
- Edison's tactic toolkit includes `lia` and `grind`.
- Commit/push **only when asked**. Dashboard `done:true` only after ground-truth build green.
- Old-file deletion only via the X-phase waves (blocker map lives in X.1a/b/c).

### Dashboard workflow

- Live Artifact: <https://claude.ai/code/artifact/5d2405e0-9c0a-4e01-9972-d03e21ed5bcf>
  (favicon 🧭, same URL always). **Account-tied** — if the account changes, republish
  `.claude/brauer-roadmap.html` as a new Artifact and record the new URL here.
- Source of truth copies: `.claude/brauer-roadmap.html` (this repo, committed) and the
  session scratchpad / memory `audit-workspace` copies (machine-local).
- Update procedure: edit the `TASKS` array (top of the script) — set `done:true`, edit **only
  `d:` fields**, NEVER renumber done task IDs (checkbox state lives in localStorage keyed by
  ID). Republish with the `Artifact` tool at the same URL, then sync all copies + this file.
- Machine-local Claude memory: `~/.claude/projects/-Users-edisone-Desktop-BrauerGroup/memory/`
  (`brauer-local-field-roadmap.md` = session-to-session log; duplicates much of this file).

---

## 4. Key API map & letter conventions

**Letter conventions (watch these!):** `CrossProductAlgebra`/`CyclicAlgebra` files use
**F = base, K = Galois top**; `FactorSet.lean`/`GoodRep` use **K = base, L = top**.

- **Foundation** (`Algebra/BrauerGroup/Basic.lean`, `BaseChange.lean`, `Relative/Basic.lean`,
  `Split.lean`, `Galois.lean`): `BrauerGroup.mk k A`, `mk_eq_mk`, `mk_congr`,
  `mk_matrix_eq_one`, `BrauerGroup.induction`, `baseChange` MonoidHom + `_self`/`_comp`,
  `relativeBrGroup K L := (baseChange K L).ker`, `Algebra.IsSplit` (Prop, cross-universe),
  `isSplit_iff_baseChange_eq_one`, `mk_mem_relativeBrGroup_iff_isSplit`,
  `IsSplit.of_isScalarTower`, `exists_finite_galois_mem`, `iSup_relativeBrGroup_eq_top`,
  `Algebra.IsCentralSimple.degree` kit, `Algebra.IsSplit.exists_embedding`
  (`Split/Embedding.lean`), `split_of_finrank`/`split_iff_finrank` (`Split/Finrank.lean`).
- **074-cluster** (`RingTheory/SimpleRing/*`, `RingTheory/SkolemNoether.lean`,
  `RingTheory/SimpleModule/Wedderburn.lean`): `skolemNoether` (forces source/target in ONE
  universe), `Subalgebra.centralizer_isSimple`, `finrank_centralizer_mul_finrank`,
  `centralizer_centralizer`, `tensorCentralizerEquiv`, `AlgHom.bijective_of_finrank_eq`,
  W-A uniqueness `IsSimpleRing.wedderburn_artin_{divisionring,size}_unique` +
  `wedderburn_artin_common_divisionring` (in `SimpleModule/WedderburnArtin.lean`; its
  existential also returns `Module.Finite k D`), and its Brauer-level packaging
  `BrauerGroup.nonempty_algEquiv_of_mk_eq_of_finrank_eq` (same class + same finrank ⟹ ≃ₐ,
  in `BrauerGroup/Basic.lean` — 4.5b).
- **CrossProductAlgebra** (`Algebra/CrossProduct/Basic.lean` + `CentralSimple.lean`):
  structure wrapping `Gal(K/F) →₀ K`; `basis`, `mulLinearMap_single_single`
  (`single σ c * single τ d = single (στ) (c · σ d · f(σ,τ))`), `one_def` coefficient
  `(f(1,1))⁻¹`, `incl`, `of : Gal → (CPA f)ˣ`, `of_mul_of`, `of_conj`, `dim_eq_sq`,
  IsCentral/IsSimpleRing under `[Fact (IsMulCocycle₂ f)]`.
  **`of_one`/`of_mul_of` are CARRIER-level equations** — for a units-level goal do
  `Units.ext` then `Units.val_mul` first.
  **Generator API (2026-07-17)**: `CrossProductAlgebra.single f σ c` (+ `val_single`,
  `single_zero/add`, `smul_single`, `single_one_eq_basis`, `single_eq_smul_basis`,
  `one_eq_single`, `single_mul_single` — the last is Fact-FREE, in Basic.lean) and
  `CrossProductAlgebra.induction_linear` (@[elab_as_elim], cases zero/add/single at CPA
  level) — never write `⟨.single σ c⟩` / `mk (.single σ c)` or induct on `.val` in consumer
  files anymore; `incl_eq_single` in CentralSimple.lean. Defining-file internals stay at
  Finsupp level; `one_def`/`mk_single_one` kept verbatim for legacy (IsoSecond).
- **FactorSet layer** (`Algebra/BrauerGroup/Relative/Cohomology/FactorSet.lean`):
  `GoodRep L x` (ι : L →ₐ[K] carrier; `Algebra L carrier` is IMPOSSIBLE in a K-central
  algebra), `self_centralize`, `conjFactor A σ`, `conjFactor_rel` (∃!),
  `conjFactor.mul/diff/diff_spec/diff_unique`, `factorSet` + `factorSet_spec`/`factorSet_unique`
  (produces `c = factorSet` — often need `.symm`), `isMulCocycle₂_factorSet`,
  `isMulCoboundary₂_factorSet_div`; §cyclic: `conjFactor.one/cast/pow`, `powFamily`,
  `powUnitL`, `powScalar : Kˣ`, `factorSet_powFamily`; §comparison:
  `GoodRep.exists_algEquiv_ι` (any two GoodReps of x isomorphic intertwining the ι's,
  stated at `GoodRep.{v}` — the skolemNoether same-universe pin), `conjFactor.map` +
  `factorSet_map` (transport preserves the factor set on the nose); §canonical:
  `GoodRep.ofCrossProduct`/`ofFamily`/`factorSet_ofFamily`.
- **Structure layer** (`Relative/Cohomology/Structure.lean`): `GoodRep.lmodule` L-action kit
  (LOCAL instances only — global would diamond with concrete carriers' native L-actions),
  `finrank_ι`, `conjFactor_coeff` (Dedekind), `linearIndependent_conjFactor`,
  `conjFactorBasis`, `compareEquiv` (+ basis/single kit), `compareAlgEquiv` (STRUCTURE
  THEOREM), `mk_crossProduct_factorSet`, `CrossProductAlgebra.mk_congr_cocycle`,
  `exists_mk_cyclicAlgebra_eq` (5.4).
- **Maps** (`Relative/Cohomology/Maps.lean`): `IsMulCocycle₂.toRelBr`, `equivOfCoboundary`,
  `relativeBrGroup.fromCocycles₂/fromH2` + `fromH2_H2π` (@[simp] spec — downstream uses ONLY
  this), `groupCohomology.H2π_surjective`.
- **Cyclic layer** (`GroupTheory/CyclicIndex.lean`, `Algebra/CrossProduct/Cyclic.lean`,
  `Algebra/BrauerGroup/Cyclic.lean`):
  `ZMod.carry : ZMod n → ZMod n → ℤ` + `carry_eq_ite`/`carry_cocycle` (ported from CFT
  LocalInv, Apache-2.0 attribution in the docstring); `genExp σ hσ : G → ZMod (orderOf σ)`
  as a `noncomputable abbrev` over mathlib's `zmodMulEquivOfGenerator` — interface is ONLY
  `genExp_pow`/`genExp_one`/`pow_genExp_val`/`genExp_mul` (`[Finite G]` needed only by
  `pow_genExp_val`); `prod_univ_eq_prod_range_pow` (P0);
  `cyclicCocycle σ hσ a := fun p ↦ (Units.map (algebraMap F K) a) ^ carry (genExp p.1) (genExp p.2)`,
  `CyclicAlgebra` (abbrev), `of_pow_eq_of`, `of_pow_orderOf` (uⁿ = a — **requires σ ≠ 1**),
  `cyclicCocycle_mul_cyclicCocycle`, P1 `prod_range_smul_eq_map_norm`,
  **`isMulCoboundary₂_cyclicCocycle_iff`** (coboundary ⟺ ∃ c, N(c) = a) + `_div_iff`;
  `oneToEnd`/`oneEquivEnd` (CPA(1) ≅ End K L) + calc kit, `BrauerGroup.mk_one_eq_one`.
- **Shim**: `Finset.prod_range_add_pow_smul` in
  `BrauerGroup/Algebra/BigOperators/GroupWithZero/Action.lean` —
  `∏_{k<m+n} gᵏ•c = (∏_{k<m} gᵏ•c) · gᵐ • ∏_{k<n} gᵏ•c` at `[Monoid G] [CommMonoid M]
  [MulDistribMulAction G M]`; conceptually `pow_add` in `M ⋊ G`. PR candidate.
- **Assembly kit** (`Topology/Instances/AddCircle/Rat.lean`,
  `Algebra/Group/Subgroup/Directed.lean`): `RatAddCircle`, `ZMod.toRatAddCircle(Equiv)`,
  `cyclic N` + `cyclic_le`/`directed_cyclic`/`iSup_cyclic`; `Subgroup.iSupLift` /
  `AddSubgroup.iSupLift`.
- **Mathlib convention** `IsMulCoboundary₂`: `∃ x, ∀ g h, g • x h / x (g*h) * x g = f (g,h)` —
  convert ONCE to multiplied form and work there.

### Useful mathlib facts confirmed in this pin

`zmodMulEquivOfGenerator` (multiplicative, with 4 simp lemmas) · `Finset.smul_prod'` ·
`IsGalois.card_aut_eq_finrank` is **Nat.card-valued** · `Algebra.norm F : K →* F` +
`norm_eq_prod_automorphisms` · `Units.map_injective` · `FaithfulSMul.algebraMap_injective` ·
`AlgHom.bijective_of_finrank_eq` (repo) · `algEquivMatrix` · `Module.finrank_linearMap` ·
`InfiniteGalois.mem_range_algebraMap_iff_fixed` (no finiteness) · `instance : Epi (H2π A)` ·
`Rep.ofAlgebraAutOnUnits` (Hilbert 90 instances keyed to it) ·
`FiniteField.norm_surjective` + `Algebra.trace_surjective` ·
`ramificationIdx_mul_inertiaDeg_of_isLocalRing` · `IsNonarchimedeanLocalField` exists with
ZERO instances · mathlib `cancelBaseChange` needs CommSemiring on BOTH factors (X.2).

---

## 5. Gotcha compendium

**Module system**
- `omit [X] in` / `include h in` go **BEFORE docstrings**; theorem bodies don't auto-include
  section variables (`include hσ in`).
- Slim-import module files need explicit `Mathlib.Tactic.Ring`/`Zify` (else "unknown tactic")
  and explicit `Mathlib.Tactic.SuppressCompilation` (else `suppress_compilation` silently
  fails → cascade of 'noncomputable' errors).
- `Mathlib.FieldTheory.Galois.Basic` does NOT pull the `Gal(K/F)` macro — import
  `…Galois.Notation` explicitly.
- Exposed public defs cannot reference private ones.

**Elaboration**
- Statement-level TC can't see proof-`haveI`s — e.g. state class equations as
  `((mk D)⁻¹)⁻¹` rather than `mk Dᵐᵒᵖ`.
- `Units.map (algebraMap F K) b` fails to elaborate where smul hides the expected type —
  ascribe `(… : Kˣ)`.
- `rw [show X = Y from rfl]` with a coercion LHS → "pattern is metavariable"; use
  `exact (lemma).trans …` on the defeq.
- `simpa using X` can eat X with its own `@[simp]` attribute (True mismatch) — use exact/trans.
- `Additive X` unfolds to X → ascribe the cocycle function + explicit `(M := Lˣ)` on the
  LowDegree bridges (see Maps.lean).
- Anonymous-constructor `_` for an ∃-bound CLASS binder is solved only by unification, never
  by TC fallback — if later components mention the instance (e.g. a `Nonempty (… Matrix … D)`
  forces `DivisionRing D`) the `_` works, otherwise (e.g. `Module.Finite k D`) pass the term
  explicitly.
- `Rep k G` is polymorphic BUT LowDegree's H²/ofMulDistribMulAction sections pin **G : Type 0**
  — keep algebra-side lemmas universe-polymorphic, specialize only the cohomology section.
- `of_ringEquiv` on subalgebra subtypes hits Mul-instance-path diamonds — inline the RingEquiv
  literal at the use site; chaining big lemma applications in one `exact` can blow whnf
  heartbeats — split into `have` steps.

**Instances / diamonds**
- **Diamond cure**: never `letI` `IsField.toField`/choice-built structures on subalgebra
  subtypes — build via `Subalgebra.divisionRingOfFinite` / `fieldOfIsMulCommutative`
  (abbrevs over the canonical Ring/CommRing via `ofIsUnitOrEqZero`).
- `RingHom.toAlgebra′` (not `toAlgebra`) when the codomain is noncommutative.
- Consumers of the §CentralSimple scoped instances need `open scoped IsMulCommutative` +
  `open scoped Subalgebra`.
- mathlib `ResidueField` has an algebra-smul diamond (CFT carries a shim workaround) — 6.5b.

**Perf**
- Never rw/▸ under `IsSimpleRing`/`finrank` of big subalgebra terms — rewrite plain
  `Subalgebra` equalities and transport by application with ascribed expected types.
  Measure with `-Dtrace.profiler.useHeartbeats=true`.

**Ops (NEVER do)**
- Never `rm -rf .lake/packages/mathlib/.lake` (holds ALL prebuilt oleans; recover with
  `lake exe cache get`). Never run `lake build` from inside the mathlib pin dir (Bash cwd
  persists between calls).
- grep can't see typeclass-only instance uses — the final arbiter for deletions is `lake build`.
- When editing the dashboard: edit only `d:` fields; a sed-style edit once clobbered 6 task IDs.

**Math traps caught (don't re-trip)**
- "C(L) commutative for commutative L" is FALSE (⊥ in M₂) — it's equivalent to
  self-centralizing.
- Max-commutative does NOT imply dim² in a mere CSA (Schur's dim-5 in M₄) — dim legs need
  `IsSimpleRing ↥L`. Maximal *subfield* is the wrong notion in a CSA (M₂(F) example).
- The CSA-general "split ↔ finrank" iff is FALSE (M₂(k) is split by k) — division algebras only.
- `of_pow_orderOf` (uⁿ = a) FAILS for σ = 1.
- Koethe needs `IsCentral` (𝔽_p(t^{1/p})/𝔽_p(t) counterexample).
- Pointwise isos do NOT determine an iSup (Prüfer vs ⊕ℤ/2ⁿ) — need directed compatibility;
  hence colimit-free Phase 8 via `iSupLift`.

---

## 6. Task board (dashboard rev 54 — 50/132)

Full mirror of the dashboard `TASKS` array. `[x]` = done (ground-truth build green).

### Phase 0 — Foundation (complete)
- [x] **0.1** BrauerGroup group structure via mk/lift/lift₂ — CommGroup on mathlib's BrauerGroup; `mk_eq_mk`, `mk_congr`, `mk_matrix_eq_one`, `induction`.
- [x] **0.2** `baseChange : BrauerGroup K →* BrauerGroup L` — matrixEquivTensorL + matrixBaseChange replace the 300-line someEquivs chain.
- [x] **0.3** `baseChange_self`, `baseChange_comp`, universe tower across three levels.

### Phase 1 — Relative Br + splitting predicate (complete)
- [x] **1.1** `relativeBrGroup K L := (baseChange K L).ker` — `Relative/Basic.lean`, + `mem_relativeBrGroup_iff`.
- [x] **1.2** `Algebra.IsSplit` Prop (cross-universe) + `IsSplit.of_algEquiv`; data-valued split dies with X.1.
- [x] **1.3** `isSplit_iff_baseChange_eq_one` — forward mk_congr + mk_matrix_eq_one; backward W-A + uniqueness.
- [x] **1.4** `isSplit_congr` + `mk_mem_relativeBrGroup_iff_isSplit`.
- [x] **1.5** `IsSplit.of_isScalarTower` — 4-step equiv chain, no k̄/deg detour.
- [x] **1.12** `IsSplit.of_isAlgClosed` — 3 lines.
- [x] **1.6** W-A uniqueness: `Matrix.divisionRing_unique` + `size_unique` (stacks 074E), `RingTheory/SimpleModule/Wedderburn.lean`.
- [x] **1.7** `IsSimpleRing.wedderburn_artin_common_divisionring` — de-Brauerized common division algebra.
- [x] **1.8** `Unique (BrauerGroup k)` for alg closed k — `AlgClosed.lean`.
- [x] **1.9** `Unique (BrauerGroup 𝔽_q)` — `FiniteField.lean`; shim `Algebra.IsCentral.of_matrix` (`Central/Matrix.lean`).
- [x] **1.10** CSA descent — `Algebra.IsCentral.of_baseChange` via linear retraction (no Nontrivial/FiniteDimensional).
- [x] **1.11** `Algebra.IsCentralSimple.degree` kit (Nat.sqrt-based, in `Split.lean`).

### Phase 2 — Skolem–Noether + double centralizer (complete)
- [x] **2.1** 074E Morita trio via mathlib Isotypic API.
- [x] **2.2** `linearEquiv_iff_finrank_eq_over_simple_ring` — via Isotypic + Hopkins–Levitzki.
- [x] **2.3** `skolemNoether` reproof — `RingTheory/SkolemNoether.lean`, regular-representation, 145 lines.
- [x] **2.4** `IsSimpleRing.left/right_of_tensor` — direct two-sided-ideal argument, universe restriction dropped.
- [x] **2.5** `Subalgebra.centralizer_range_lmul` (~10 lines, no simplicity/finiteness) + `Algebra.rmul` (`Algebra/Algebra/Opposite.lean`).
- [x] **2.6** `Subalgebra.centralizer_isSimple` (074S) — `RingTheory/SimpleRing/Centralizer.lean`; + `IsSimpleRing (Module.End R M)` via `endRingEquivMatrixOpposite` (`ToLin.lean`).
- [x] **2.7** `Subalgebra.finrank_centralizer_mul_finrank` — with `AlgHom.range_conj`/`conj_centralizer`/`finrank_conj`.
- [x] **2.8** `Subalgebra.centralizer_centralizer` — plus the perf pass (see gotchas).
- [x] **2.9** `Subalgebra.tensorCentralizerEquiv` (074U) via `AlgHom.bijective_of_finrank_eq`; old DoubleCentralizer.lean deleted; center-of-simple instances → `SimpleRing/Center.lean`.
- [x] **2.10** `Subalgebra.conj` API via ConjAct — `Subalgebra/Conj.lean`, incl. general `map_centralizer`.

### Phase 3 — Maximal commutative subalgebras, Koethe, Br = ⋃ (complete)
- [x] **3.1** `exists_maximal_comm_subalgebra` — Zorn, `Subalgebra/Directed.lean`; NO SubField structure anywhere (Zulip consensus).
- [x] **3.2** Scoped instances: `Algebra ↥L ↥(centralizer F L)` (toAlgebra′) + `isCentral_centralizer` — §CentralSimple.
- [x] **3.3** commutative ⟹ field — superseded by diamond-safe `fieldOfIsMulCommutative` (`Subalgebra/DivisionRing.lean`).
- [x] **3.4** Keystone: MC ↔ self-centralizing (`Subalgebra/Lattice.lean`, mathlib-ready) ↔ dim² for simple L (`isMaximal_comm_iff_finrank`).
- [x] **3.5** dim_max_subfield — absorbed inline into 3.7.
- [x] **3.6** Koethe: `DivisionRing.exists_separable_maxSubfield` (`Subalgebra/DivisionRing.lean`) — Zorn + Jacobson–Noether on the centralizer + diamond cure.
- [x] **3.7** `exists_finite_sep_split` + `exists_finite_galois_split` (`Split/DivisionRing.lean`) — [Algebra.IsAlgebraic k k̄] required; compositum separability via isSeparable_iSup.
- [x] **3.8** `split_of_finrank` / `split_iff_finrank` (division only!) — Shape-A design (`Split/Finrank.lean`).
- [x] **3.9** isSplit-of-max-comm — inline in 3.7; extract when a consumer appears.
- [x] **3.10** Directed-union tensor descent — obsolete, closed.
- [x] **3.11** Finite-extension splitting — absorbed by 3.7.
- [x] **3.12** `exists_finite_galois_mem` + `iSup_relativeBrGroup_eq_top` (`BrauerGroup/Galois.lean`) — **PHASE 3 COMPLETE**.

### Phase 4 — TRUNK: crossed products (10/17)
- [x] **4.1** CrossProductAlgebra ported + split into `CrossProduct/Basic.lean` (no cocycle hyp) + `CentralSimple.lean`; `RingCon.mkL` shim promoted.
- [x] **4.2** GoodRep + `nonempty` via NEW `Algebra.IsSplit.exists_embedding` (`Split/Embedding.lean`) — op-twist proof, `endAlgEquivMatrixOpposite`; d ∣ [L:K] extractable for Phase 6.
- [x] **4.3** conjFactor + diff/mul API + factorSet + master equation (`FactorSet.lean`).
- [x] **4.4a** `isMulCocycle₂_factorSet` — double-association expansion, erw-free.
- [x] **4.5a** `isMulCoboundary₂_factorSet_div` — same-GoodRep comparison.
- [x] **4.5b** W-A packaging — Done 2026-07-15 (Edison + Fable): `BrauerGroup.nonempty_algEquiv_of_mk_eq_of_finrank_eq` in `BrauerGroup/Basic.lean`; mk_eq_mk destructure → common_divisionring → dimension count → `reindexAlgEquiv`/`finCongr` finish. `common_divisionring` upgraded to return `Module.Finite k D` (pass the binder explicitly — see gotchas); `Wedderburn.lean` renamed `WedderburnArtin.lean`.
- [x] **4.5c** Skolem–Noether alignment — Done 2026-07-15: `GoodRep.exists_algEquiv_ι` (FactorSet.lean §comparison); 4.5b on the `quot_eq`/`dim_eq_sq` projections + `skolemNoether` correction via `MulSemiringAction.toAlgEquiv (ConjAct.toConjAct u)`. `GoodRep.{v}` pin kept (Subsingleton-split bypass analyzed and rejected; ULift / two-universe skolemNoether are the real escape hatches if ever needed).
- [x] **4.5d** factorSet transport — Done 2026-07-15 (Edison): `conjFactor.map` (+ `@[simp] map_val`) and `factorSet_map` in §comparison; transported family has the SAME factor set on the nose. No universe pin (same x forces same universe via `quot_eq`). Gotcha: `← map_inv` before `Units.coe_map`.
- [x] **4.5e** Cross-GoodRep coboundary comparison — Done 2026-07-15 (Edison): `isMulCoboundary₂_factorSet_div'` in §comparison, 3 lines (`exists_algEquiv_ι` + `rw [← factorSet_map]` + 4.5a). **Chain closed.**
- [x] **4.7a** L-module kit — Done 2026-07-15 (Edison): NEW `Relative/Cohomology/Structure.lean` (4.7+4.8 home, not in root yet): `GoodRep.lmodule` + `lsmul_def` + tower/finiteness + `finrank_ι`, all `attribute [local instance]` only (global would diamond with CPA's native L-action).
- [x] **4.7b** Dedekind coefficient lemma — Done 2026-07-15 (Edison): `GoodRep.conjFactor_coeff` (Structure.lean); Finsupp shape matched to `linearIndepOn_iff`, τ-dependent family via `Finsupp.onFinset`.
- [x] **4.7c** conjFactor independence — Done 2026-07-15 (Edison): `GoodRep.linearIndependent_conjFactor`, 23 lines, finiteness-free (maximal `linearIndepOn` subfamily + field rescale + 4.7b + `mul_right_cancel₀`).
- [x] **4.7d** `conjFactorBasis` — Done 2026-07-15 (Edison): + `@[simp] conjFactorBasis_apply`. **4.7 complete: A = ⊕_σ L·u_σ.**
- [x] **4.8a** Comparison linear equiv — Done 2026-07-16 (Edison): `GoodRep.compareEquiv` + basis/single apply kit (Structure.lean); no Fact needed, restrictScalars free via the generic CPA tower instance.
- [x] **4.8b** Multiplicativity — Done 2026-07-17 (Edison): `GoodRep.compareAlgEquiv`, THE STRUCTURE THEOREM; double `induction_linear` + `single` kit, ~14 lines. Global `Fact (IsMulCocycle₂ (factorSet A b))` instance declared.
- [x] **4.8c** Structure-theorem corollary — Done 2026-07-17 (Edison): `GoodRep.mk_crossProduct_factorSet` + the `mk_congr_cocycle` shield (`subst h; rfl`) for cocycle-rewrites under `mk`.
- [x] **4.9a** CPA as its own GoodRep — Done 2026-07-15 (Edison): `GoodRep.ofCrossProduct f (h : mk K (CPA f) = x)` (h-parameterized — lets two CPAs sit over one class) + `ofFamily` + `@[simp] ofFamily_val`, FactorSet.lean §canonical.
- [x] **4.9b** factorSet of canonical conjFactors = f — Done 2026-07-15 (Edison): `factorSet_ofFamily`, 3 lines (`of_mul_of` IS the obligation).
- [x] **4.10** `fromH2 : H² → relativeBrGroup` on H2 itself (`Maps.lean`) — toRelBr, equivOfCoboundary, fromH2_H2π spec; H2π_surjective 1-liner (PR candidate). NO H2Iso/moduleCatLeftHomologyData anywhere.
- [ ] **4.11a** Bimodule M := (A ⊗[K] B) ⧸ middle-L relations, right (A⊗B)ᵐᵒᵖ-action. 2–3 steps.
- [ ] **4.11b** Left CPA(αβ)-action on M — the old 1.2M-hb C_mul_smul′, retamed via master-equation rewrites. 3 steps. **The heart of 4.11.**
- [ ] **4.11c** Bimodule glue + dim M = [L:K]³. 2–3 steps.
- [ ] **4.11d** End computation via Isotypic + repo Morita/End.lean — NO choose ladders. 3 steps.
- [ ] **4.11e** Multiplicativity `mk(CPA α)·mk(CPA β) = mk(CPA αβ)` — bijective_of_finrank_eq both sides [L:K]⁴. 3 steps. **← gates 5.7**
- [x] **4.13** Cohomology files wired into root — #min_imports pass, mk_all, build 8722, **checkpoint f831c29**.
- [ ] **4.14a** Inflation I: define `inflate` (cocycles along restrictNormalHom + Units.map; 5.6 consumes the def) + W := L′ ⊗[L] A_f with left CPA(inf f)-action; W free of rank [L′:L]. 2–3 steps.
- [ ] **4.14b** Inflation II: CPA(inf f) ~ CPA(f) — CPA(inf f) →ₐ End_{A_f}(W) ≅ M_{[L′:L]}(A_f), injective + dims. Replaces old cohomological 6.9. **← gates 5.6, B.7.** 2–3 steps.

### Phase 5 — Goal A cyclic layer (4/7; remainder trunk-gated)
- [x] **5.1** `CyclicAlgebra (σ, a)` := CPA of the carry cocycle — `CyclicIndex.lean` + `CrossProduct/Cyclic.lean`; presentation `of_pow_eq_of`, `of_pow_orderOf` (σ ≠ 1!).
- [x] **5.2** CPA(1) ≅ `End K L` + `BrauerGroup.mk_one_eq_one` (`BrauerGroup/Cyclic.lean`, Edison) + oneEquivEnd calc kit.
- [x] **5.3** Power family uⁱ + `powScalar` + `factorSet_powFamily` (`FactorSet.lean` §cyclic, Edison + carry-case fill) — ℤ-power induction, no finiteness in descent.
- [x] **5.4** Every class in Br(L/K) cyclic — Done 2026-07-17 (Edison): `exists_mk_cyclicAlgebra_eq` (Structure.lean, single universe from `GoodRep.nonempty`), witness `powScalar σ hσ A u`, 6 lines.
- [x] **5.5a** Cyclic coboundary ⟺ norm — `isMulCoboundary₂_cyclicCocycle_iff` + `_div_iff`; P0/P1/P2 prep, coboundary_aux telescope, recurrence + (σⁿ⁻¹,σ) evaluation, Units.map_injective. Build 8723.
- [x] **5.5b** 🏁 Split iff norm — Done 2026-07-15 (Edison): `CyclicAlgebra.mk_eq_one_iff` in `Algebra/BrauerGroup/Cyclic.lean`; `rw [← isMulCoboundary₂_cyclicCocycle_iff]` up front, (⇒) via 4.5e + 4.9 with the CPA(1) GoodRep in the first slot, (⇐) via `equivOfCoboundary` + `mk_one_eq_one`. File slimmed to 6 imports by #min_imports.
- [ ] **5.6** Cyclic inflation formula [(L/K,σ,a)] = [(L′/K,σ′,a^{[L′:L]})] — explicit coboundary β(σ′ⁱ) = a^⌊i/n⌋ + **4.14b**. Feeds 8.2b. 2–3 steps.
- [ ] **5.7** Multiplicativity [(σ,a)]·[(σ,b)] = [(σ,ab)] — instance of **4.11e** (cocycle half shipped with 5.1). 1 step.

### Phase 6 — Local fields + CFT port + Frobenius + wall #3 (0/17 open here)
- [ ] **6.1** `IsNonarchimedeanLocalField ℚ_[p]`: **proof COMPLETE** in `Algebra/test.lean` (Edison; builds green) — remaining is cleanup/golf/rehome/slim imports only; decide spelling vs CFT's `NormedField.isValuativeTopology` shim. Closes CFT Basic.lean:66 sorry — PR back. 1–2 steps.
- [ ] **6.2a** ValuativeRel + IsValuativeTopology for 𝔽_q⸨t⸩. 2 steps.
- [ ] **6.2b** Integers ≅ K⟦X⟧, residue ≅ K. 2–3 steps.
- [ ] **6.2c** `IsNonarchimedeanLocalField 𝔽_q⸨t⸩` — local compactness in reverse. 2 steps.
- [ ] **6.3a** CFT port wave 1: ~15 shims (HenselPolynomial 767-line engine, roots-of-unity, DVR/uniformizer, NormedValued, ResidueField-diamond workaround…); DROP already-upstreamed ones. Mechanical + pin drift.
- [ ] **6.3b** CFT port wave 2: local-field core (Basic minus its ℚ_p sorry, Valuation SES, Adic, Actions, Tower, IntermediateField, Continuity) + merge test.lean's `isNonarch_of_finiteDimensional` ([ValuativeExtension]+[IsModuleTopology]+[IsRankLeOne] — naive statement FALSE).
- [ ] **6.3c** CFT port wave 3: `UnramifiedExtension K n := SplittingField(X^{q^n−1}−1)` (finrank = n, f = n, e = 1, IsGalois, universal property, maximalUnramified), RamificationInertia, Teichmüller (fields).
- [ ] **6.3d** Fill `Module.Finite 𝒪[K] 𝒪[L]` — THE load-bearing CFT sorry ("power series shenanigans"); everything e/f sits on it. 3 steps.
- [ ] **6.5a** De-choice the unramified tower data (CFT's .choose-based structures → canonical data; spec-lemma discipline). 2 steps.
- [ ] **6.5b** Reduction iso Gal(K_n/K) ≅ Gal(𝕜_n/𝕜) — injective (e = 1 kills inertia), surjective by count; WATCH the ResidueField smul diamond. 3 steps.
- [ ] **6.5c** Frobenius generator; Gal(K_n/K) ≅ ZMod n, generator-explicit — the σ Phase 5 consumes. Absent from CFT. 1–2 steps.
- [ ] **6.5d** Frobenius-compatible tower K_n ↪ K_m (n ∣ m) — consumed by 5.6-gluing, 7.10, 8.2b. 2–3 steps.
- [ ] **6.6a** Residue norm & trace surjectivity — both in pin; instantiate. 1 step.
- [ ] **6.6b** One-step approximation for unit norms mod 𝔪^{i+1}. 2–3 steps.
- [ ] **6.6c** Limit: N : 𝒪_{K_n}ˣ ↠ 𝒪_Kˣ — **WALL #3 falls here**; CFT has it sorried on BOTH routes; first solver shares upstream. 2 steps.
- [ ] **6.7a** N(K_nˣ) = 𝒪_Kˣ · ϖ^{nℤ}. 2 steps.
- [ ] **6.7b** Kˣ/N(K_nˣ) ≅ ZMod n via the valuation, generator-explicit (ϖ ↦ 1). 1–2 steps.
- [ ] **6.8** 🏁 `invₙ : Br(Kₙ/K) ≃* ZMod n` via cyclic algebras — r ↦ [(Kₙ/K, Frob, ϖʳ)]; surjective (5.4 + 6.7a), injective (5.5b + 6.7b), hom (5.7). NO cohomology anywhere. 2–3 steps.

### Phase 7 — Reduced norm valuation ⇒ unramified splitting (0/17 open)
- [ ] **7.1a** Migrate ReducedCharPoly to the degree kit — kills F_bar/IsAlgClosure hyps in the already-proved eq_pow_reducedCharpoly/eq_polys/mem_Kx; unblocks X.1a. Mostly mechanical.
- [ ] **7.1b** Clean common overfield E := (F ⊗[K] L)/max with a REAL Field instance (no IsField.toField hacks). 2 steps.
- [ ] **7.1c** Finish `unique_onver_split` — replaces 3 sorries. 3 steps.
- [ ] **7.2** Coefficients descend to K — already proved in old file; 7.1a carries it. 1 step.
- [ ] **7.3** K-valued reducedNorm/reducedTrace (multiplicativity layer already proved F-valued). 2–3 steps.
- [ ] **7.4a** Unit ⟹ Nrd ≠ 0. 1 step.
- [ ] **7.4b** Nrd ≠ 0 ⟹ unit — Cayley–Hamilton/adjugate. 2–3 steps.
- [ ] **7.5a** Nrd under scalar extension. 1–2 steps.
- [ ] **7.5b** Nrd under algEquiv; trace analogues. 2 steps.
- [ ] **7.6a** ReducedCharPoly of a subfield element = (minpoly)^{n/m}. 3 steps.
- [ ] **7.6b** Nrd(x) = N_{K(x)/K}(x)^{n/m} — bridge to commutative valuation theory. 1–2 steps.
- [ ] **7.7a** w := (1/n)·v∘Nrd multiplicative, extends v. 1–2 steps.
- [ ] **7.7b** w|K(x) is THE canonical extension valuation (spectral-norm uniqueness via 6.3). 2–3 steps.
- [ ] **7.7c** w is a valuation on D (ultrametric via K(x)). 2 steps.
- [ ] **7.8a** 𝒪_D, 𝔪_D, residue division ring. 2–3 steps.
- [ ] **7.8b** Residue of D is a finite field — bounded degree + littleWedderburn. 1–2 steps.
- [ ] **7.9a** e·f accounting: e = f = n. 3 steps.
- [ ] **7.9b** Unramified maximal subfield of D — Teichmüller/Hensel lift (6.3c template transfers). 3 steps.
- [ ] **7.9c** D split by K_n — K(x) ≅ K_n (uniqueness + 6.5d) + maximal-subfield-splits (3.9). Uses 4.5b. 2 steps.
- [ ] **7.10** 🏁 Br(K) = ⋃ₙ Br(Kₙ/K) — divisibility-directed system for 8.2. 2–3 steps.

### Phase 8 — Goal A assembly (2/7)
- [x] **8.1** ZMod n ↪ AddCircle (1:ℚ) with n ∣ m compatibility — `Topology/Instances/AddCircle/Rat.lean` (RatAddCircle, toRatAddCircle(Equiv), cyclic N, iSup_cyclic = ⊤). Gotcha: zmultiples-membership goals are beta-redexes.
- [ ] **8.2a** Level maps eₙ := invₙ ∘ toRatAddCircle (all Multiplicative/Additive bookkeeping HERE). 1–2 steps.
- [ ] **8.2b** Tower compatibility of the eₙ — 5.6 on the Frob-compatible tower + cyclic_le. 2 steps.
- [ ] **8.2c** Glue: `inv : Br(K) →* Multiplicative ℚ/ℤ` — iSupLift over 7.10. 1–2 steps.
- [ ] **8.3** 🏁 **GOAL A**: `BrauerGroup K ≃* Multiplicative (AddCircle (1:ℚ))`. 2–3 steps.
- [ ] **8.4** Invariant API: inv of degree-n cyclic = 1/n; order = index.
- [x] **8.5** `Subgroup.iSupLift`/`AddSubgroup.iSupLift` (`Subgroup/Directed.lean`, to_additive). PR candidate.

### Phase B — Goal B: Br ≅ H² (0/10; 4.10 already done in trunk)
- [ ] **B.1** toCocycles₂ packaging (Type-0 section; Additive trap). ≤1 step.
- [ ] **B.2** `toH2` + spec lemma toH2_eq for EVERY GoodRep/family (uses 4.5e). 2–3 steps.
- [ ] **B.3** Round trip fromH2 ∘ toH2 = id (toH2_eq + 4.8c). 2 steps.
- [ ] **B.4** Round trip toH2 ∘ fromH2 = id (H2_induction_on + 4.9b). 2 steps.
- [ ] **B.5** 🏁 `Br(L/K) ≃* H²(Gal(L/K), Lˣ)` over an ARBITRARY base field — MulEquiv.mk′ + 4.11e. **Prime mathlib PR.** 1–2 steps.
- [ ] **B.6** Port CFT inflation/restriction (PROVED there); SKIP their sorried inf-res exactness — injectivity comes from the Brauer side.
- [ ] **B.7** B.5 commutes with inflation — algebra half = 4.14b, cohomology half = B.6. 2–3 steps.
- [ ] **B.8** 🏁 **GOAL B**: Br(K) ≅ colim H² over finite Galois subextensions (Module.DirectLimit; NO profinite topology); ℚ/ℤ corollary free from Goal A. 3 steps.
- [ ] **B.9** Continuous-cohomology upgrade — quarantined, never a blocker. (True fact: for profinite G and discrete modules, continuous cochain cohomology = colim of finite-level; the comparison iso is what mathlib's young ContCohomology still lacks.)
- [ ] **B.10** Optional invariant comparison cyclic inv = cohomological inv — via CFT's PROVED carry localInv (H²(ℤ/n,ℤ) ≃+ ZMod n).

### Phase X — Deletions + upstreaming
- [ ] **X.1a** Deletion wave 1 (after 7.1a): SplittingOfCSA + AlgClosedUnion + ExtendScalar.
- [ ] **X.1b** Deletion wave 2 (after 4.x/B.5): ToSecond, IsoSecond, RelativeBrauer, Subfield quartet + 2 shims. BLOCKER: FrobeniusTheorem pins the quartet — port or keep a rump, decide then.
- [ ] **X.1c** Deletion wave 3: FrobeniusTheorem decision, BrauerOverR, AbsoluteIsoH2 stub, CentralSimple remnants.
- [ ] **X.2** Generalize mathlib's `cancelBaseChange` to noncommutative B (pin demands CommSemiring both factors — verified TensorProduct/Maps.lean:466; does NOT replace absorb_eqv yet).
- [ ] **X.3** Upstream PR batch — see §7.

---

## 7. Mathlib PR batch (X.3 running list)

W-A uniqueness · Skolem–Noether · double-centralizer cluster (074S/074U) ·
`Algebra.IsCentral.of_matrix` · `of_baseChange` · crossed products ·
`Subgroup/AddSubgroup.iSupLift` · `RatAddCircle` torsion kit · `RingCon.mkL` ·
`H2π_surjective` · `endAlgEquivMatrixOpposite` · `Subalgebra/Lattice.lean` MC↔SC file ·
diamond-cure `divisionRingOfFinite`/`fieldOfIsMulCommutative` ·
`Finset.prod_range_add_pow_smul` (deluxe version: `SemidirectProduct.left_pow` — no pow
lemmas exist there) · `prod_univ_eq_prod_range_pow` · `ZMod.carry` kit ·
`NeZero (orderOf σ)` instance · `IsNonarchimedeanLocalField` instances (6.1 back to CFT too) ·
B.5 itself · `Subfield.centralizer` idea.

---

## 8. External resources

- **ClassFieldTheory repo**: <https://github.com/kbuzzard/ClassFieldTheory> — Apache-2.0,
  **Edison is an author** (no copyright issue; keep attribution headers as in
  `CyclicIndex.lean`). Pin 23b0068d, one generation behind ours; same module system.
  Survey verdict: ~90% of the local-field tree is proved (spectralNorm finite-ext,
  e/f + e·f = [L:K] modulo the 6.3d sorry, UnramifiedExtension via roots of unity,
  Teichmüller for fields, Valuation SES, Actions); **zero Brauer content**; inf-res
  exactness sorried (not needed); carry-cocycle localInv PROVED. Clone fresh when porting
  (old clone was in a session scratchpad, gone).
- **Edison's ℚ_p local-field proof**: now living in `BrauerGroup/Algebra/test.lean` (6.1).
- **Zulip spectator API recipe** (for consensus archaeology): prepend
  `{"operator":"streams","operand":"web-public"}` to the narrow; cookie `__Host-csrftoken` +
  `X-CSRFToken` header on GET `/json/messages`.
- **Old-repo survey data**: per-decl port/reprove/drop verdicts were produced by 12/13-agent
  workflow runs; the durable conclusions are all baked into the task board above.
- **Claude memory (machine-local)**: `~/.claude/projects/-Users-edisone-Desktop-BrauerGroup/memory/`.

---

## 9. Checkpoint history

| Date | Commit | Content |
|---|---|---|
| 2026-07-08/09 | (several) | Phases 0–1, clean rebuild; collaborator rebase incident resolved (kept pin cef1e7de, force-push) |
| 2026-07-11 | 79bc86a | Phase-3 opening batch (8.1, 8.5, 3.1–3.4 keystones) |
| 2026-07-11 | b6afa84 | Phase 3 complete + X-phase deletions wave 0 |
| 2026-07-14 | f831c29 | b6afa84→now batch: CrossProduct split, galAct removal, Relative rehoming, Maps/FactorSet/Embedding, CyclicIndex, cyclic layer, test.lean, min_imports + mk_all (4.13) |
| 2026-07-14 | 39ff8ce | 5.5a proof + P0 + `prod_range_add_pow_smul` shim (at `Algebra/BigOperators/`) + `.claude/ROADMAP.md` + dashboard snapshot + .gitignore exceptions |
| 2026-07-15 | ba259cd | The whole day's batch: 4.5b/c/d/e comparison chain (+ `Module.Finite k D` in common_divisionring, `WedderburnArtin.lean` rename), 4.9a/b canonical GoodRep, 🏁 5.5b `CyclicAlgebra.mk_eq_one_iff` (split iff norm), #min_imports pass |
