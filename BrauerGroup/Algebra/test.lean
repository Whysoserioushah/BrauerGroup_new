module

public import Mathlib

@[expose] public section

/-!
# `ℚ_[p]` is a nonarchimedean local field, and finite extensions of local fields

`IsNonarchimedeanLocalField K` (mathlib, `Mathlib/NumberTheory/LocalField/Basic.lean`) is
`class ... [Field K] [ValuativeRel K] [TopologicalSpace K] : Prop extends`
`IsValuativeTopology K, LocallyCompactSpace K, ValuativeRel.IsNontrivial K`.

* **Task 1** (`ℚ_[p]`): `LocallyCompactSpace ℚ_[p]` (from `ProperSpace ℚ_[p]`) and
  `ValuativeRel.IsNontrivial ℚ_[p]` are already instances in mathlib. The only missing parent is
  `IsValuativeTopology ℚ_[p]` — mathlib does *not* provide it (the `ValuativeRel ℚ_[p]` instance is
  built from `Padic.mulValuation`, but the norm-topology = valuation-topology bridge is a `TODO` in
  `Mathlib/NumberTheory/Padics/ValuativeRel.lean`). We prove it below via
  `IsValuativeTopology.of_zero` and the dictionary `‖x‖ = p ^ log (mulValuation x)`. Task 1 is then
  just assembly.

* **Task 2** (finite extensions): the statement *as originally written* is **not provable** (see the
  note above `isNonarch_of_finiteDimensional`); with the compatibility hypotheses that make it true
  it **is** proved below, the crux being that the given topology on `L` coincides with the valuation
  topology because both are the `K`-module topology.
-/

open ValuativeRel Filter Topology Metric Set
open scoped NNReal

section Task1

variable {p : ℕ} [Fact p.Prime]

/-- Strict comparison of `Padic.mulValuation` matches strict comparison of the norm on `ℚ_[p]`. -/
private lemma mulValuation_lt_iff_norm_lt (z a : ℚ_[p]) :
    Padic.mulValuation z < Padic.mulValuation a ↔ ‖z‖ < ‖a‖ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hvz : ∀ x : ℚ_[p], Padic.mulValuation x = 0 ↔ x = 0 := fun x => by simp [Padic.mulValuation]
  rcases eq_or_ne a 0 with rfl | ha
  · rw [map_zero, norm_zero]
    exact iff_of_false (not_lt.mpr zero_le) (not_lt.mpr (norm_nonneg _))
  rcases eq_or_ne z 0 with rfl | hz
  · rw [map_zero, norm_zero]
    exact ⟨fun h => norm_pos_iff.mpr ((hvz a).not.mp (pos_iff_ne_zero.mp h)),
           fun h => pos_iff_ne_zero.mpr ((hvz a).not.mpr (norm_pos_iff.mp h))⟩
  · rw [Padic.norm_eq_zpow_log_mulValuation hz, Padic.norm_eq_zpow_log_mulValuation ha,
      zpow_lt_zpow_iff_right₀ hp1,
      WithZero.log_lt_log ((hvz z).not.mpr hz) ((hvz a).not.mpr ha)]

/-- Strict comparison of the canonical `ValuativeRel` valuation matches that of the norm. -/
private lemma valuation_lt_iff_norm_lt (z a : ℚ_[p]) :
    valuation ℚ_[p] z < valuation ℚ_[p] a ↔ ‖z‖ < ‖a‖ := by
  rw [← mulValuation_lt_iff_norm_lt, ← Padic.mulValuation.vlt_iff_lt,
    ← (valuation ℚ_[p]).vlt_iff_lt]

/-- The norm topology on `ℚ_[p]` is the valuative topology of its canonical valuation. -/
instance : IsValuativeTopology ℚ_[p] := by
  apply IsValuativeTopology.of_zero
  intro s
  constructor
  · -- `s ∈ 𝓝 0` ⟹ some valuation-ball sits inside it: shrink a norm ball to a valuation-ball.
    intro hs
    rw [Metric.mem_nhds_iff] at hs
    obtain ⟨ε, hε, hεs⟩ := hs
    obtain ⟨a, ha0, haε⟩ := NormedField.exists_norm_lt ℚ_[p] hε
    have ha0' : a ≠ 0 := norm_pos_iff.mp ha0
    refine ⟨Units.mk0 (valuation ℚ_[p] a) (by simpa [valuation_eq_zero_iff] using ha0'), ?_⟩
    intro z hz
    apply hεs
    simp only [Units.val_mk0, mem_ofPred_eq, valuation_lt_iff_norm_lt] at hz
    exact mem_ball_zero_iff.mpr (hz.trans haε)
  · -- conversely each valuation-ball is a norm ball `ball 0 ‖a‖`, hence a neighbourhood of `0`.
    rintro ⟨γ, hγ⟩
    obtain ⟨a, ha⟩ := valuation_surjective (γ : ValueGroupWithZero ℚ_[p])
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero] at ha
      exact (Units.ne_zero γ) ha.symm
    refine Filter.mem_of_superset ?_ hγ
    have hset : {z : ℚ_[p] | valuation ℚ_[p] z < (γ : ValueGroupWithZero ℚ_[p])}
        = Metric.ball 0 ‖a‖ := by
      ext z
      simp only [mem_ofPred_eq, ← ha, valuation_lt_iff_norm_lt, mem_ball_zero_iff]
    rw [hset]
    exact Metric.ball_mem_nhds 0 (norm_pos_iff.mpr ha0)

/-- **Task 1:** the field of `p`-adic numbers is a nonarchimedean local field. -/
instance padic_isNonarchimedeanLocalField : IsNonarchimedeanLocalField ℚ_[p] where

end Task1

section Task2

/-!
## Task 2 — finite extensions

The requested statement
```
lemma isNonarch_of_findim (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
    [TopologicalSpace L] : IsNonarchimedeanLocalField L
```
is **false as stated**: `[ValuativeRel L]` and `[TopologicalSpace L]` are unconstrained, so `L` may
carry a valuation/topology *unrelated* to `K` (e.g. the trivial valuation, or the discrete
topology), and then all three conclusions fail. In fact `IsValuativeTopology L` is genuinely false
unless
`L`'s valuation has rank `≤ 1`: a rank-`2` valuation extending `K`'s satisfies `ValuativeExtension`
and `IsModuleTopology` yet its valuation topology is strictly finer than the module topology. So the
honest hypotheses that make the theorem *true* are:

* `[ValuativeExtension K L]` — `L`'s valuation restricts to `K`'s along `algebraMap K L`;
* `[IsModuleTopology K L]` — `L` carries the `K`-module topology;
* `[ValuativeRel.IsRankLeOne L]` — `L`'s valuation has rank `≤ 1` (automatic for finite extensions,
  but not available from the `ValuativeExtension` API, which only transfers rank downward);
* a uniformity on `K` (`[UniformSpace K] [IsUniformAddGroup K]`) to access `CompleteSpace K`.

The proof has three parts: nontriviality transfers up the value-group embedding; local compactness
is `LocallyCompactSpace.of_finiteDimensional_of_complete` over the (normed) field `K`; and the
valuative topology is identified with the given one by showing both are the `K`-module topology —
the module topology via `IsModuleTopology`, the valuation topology via
`isModuleTopologyOfFiniteDimensional`, whose hypotheses (`T2`, `IsTopologicalAddGroup`,
`ContinuousSMul`) hold because `K`'s value scale is cofinal below every element of `L`'s (this is
where `IsRankLeOne L` is essential).
-/

/-- **Task 2 (corrected):** a finite extension `L` of a nonarchimedean local field `K`, carrying the
compatible valuation (`ValuativeExtension K L`), the `K`-module topology (`IsModuleTopology K L`),
and a rank-`≤ 1` valuation, is itself a nonarchimedean local field. -/
lemma isNonarch_of_finiteDimensional
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [ValuativeRel K] [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [ValuativeExtension K L] [IsModuleTopology K L]
    [ValuativeRel.IsRankLeOne L] :
    IsNonarchimedeanLocalField L := by
  -- (e) Nontriviality of `L`'s valuation, pushed up from `K` along `mapValueGroupWithZero`.
  haveI : ValuativeRel.IsNontrivial L := by
    obtain ⟨a, ha0, ha1⟩ := (inferInstance : ValuativeRel.IsNontrivial K).condition
    refine ⟨⟨ValuativeExtension.mapValueGroupWithZero K L a, ?_, ?_⟩⟩
    · simpa using
        (ValuativeExtension.mapValueGroupWithZero_strictMono (A := K) (B := L)).injective.ne ha0
    · simpa using
        (ValuativeExtension.mapValueGroupWithZero_strictMono (A := K) (B := L)).injective.ne ha1
  -- (d) Local compactness of `L`: `K` is a complete, locally compact nontrivially normed field
  -- (its norm topology is defeq to the given one), and `L` is finite-dimensional over it.
  haveI : LocallyCompactSpace L := by
    letI : (Valued.v (R := K)).RankOne :=
      { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
        strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
            MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
    letI : NontriviallyNormedField K := Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
    haveI : IsTopologicalAddGroup L := IsModuleTopology.topologicalAddGroup K L
    exact LocallyCompactSpace.of_finiteDimensional_of_complete K L
  -- (c) The given topology on `L` is the valuative topology of `valuation L`.
  haveI : IsValuativeTopology L := by
    letI : (Valued.v (R := K)).RankOne :=
      { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
        strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
            MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
    letI : NontriviallyNormedField K := Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
    haveI hAddG : IsTopologicalAddGroup L := IsModuleTopology.topologicalAddGroup K L
    -- The given topology equals the valuation topology, because both are the `K`-module topology.
    have hEq : (inferInstance : TopologicalSpace L) = ValuativeRel.topologicalSpace L := by
      have h_given : (inferInstance : TopologicalSpace L) = moduleTopology K L :=
        eq_moduleTopology K L
      have h_v : ValuativeRel.topologicalSpace L = moduleTopology K L := by
        letI τv : TopologicalSpace L := ValuativeRel.topologicalSpace L
        haveI a1 : IsTopologicalAddGroup L := inferInstance
        haveI a2 : T2Space L := by
          apply IsTopologicalAddGroup.t2Space_of_zero_sep
          intro x x_ne
          refine ⟨{ y | valuation L y < valuation L x }, ?_, by simp⟩
          rw [IsValuativeTopology.mem_nhds_zero_iff]
          exact ⟨Units.mk0 (valuation L x) (by simpa [valuation_eq_zero_iff] using x_ne),
            fun y hy => by simpa using hy⟩
        haveI a3 : ContinuousSMul K L := by
          -- `algebraMap K L` is continuous: `K`'s valuation balls map into `L`'s, because `K`'s
          -- value scale is cofinal below every `γ ∈ (ValueGroupWithZero L)ˣ` (needs
          -- `IsRankLeOne L`).
          have halg : Continuous (algebraMap K L) := by
            apply continuous_of_continuousAt_zero (algebraMap K L : K →+ L)
            unfold ContinuousAt
            rw [map_zero, (IsValuativeTopology.hasBasis_nhds_zero K).tendsto_iff
                (IsValuativeTopology.hasBasis_nhds_zero L)]
            intro γ _
            obtain ⟨fL⟩ := (IsRankLeOne.nonempty : Nonempty (RankLeOneStruct L))
            obtain ⟨c, hc0, hc1⟩ := IsNontrivial.exists_lt_one (R := K)
            have hemc1 : fL.emb (ValuativeExtension.mapValueGroupWithZero K L c) < 1 :=
              calc fL.emb (ValuativeExtension.mapValueGroupWithZero K L c)
                  < fL.emb (ValuativeExtension.mapValueGroupWithZero K L 1) :=
                    fL.strictMono (ValuativeExtension.mapValueGroupWithZero_strictMono hc1)
                _ = 1 := by rw [map_one, map_one]
            have hγ0 : (0 : ℝ≥0) < fL.emb (γ : ValueGroupWithZero L) :=
              calc (0 : ℝ≥0) = fL.emb 0 := (map_zero _).symm
                _ < fL.emb (γ : ValueGroupWithZero L) :=
                  fL.strictMono (zero_lt_iff.mpr (Units.ne_zero γ))
            obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hγ0 hemc1
            refine ⟨Units.mk0 (c ^ n) (pow_ne_zero n hc0.ne'), trivial, ?_⟩
            intro k hk
            simp only [Set.mem_ofPred_eq, Units.val_mk0] at hk ⊢
            change valuation L (algebraMap K L k) < (γ : ValueGroupWithZero L)
            rw [← ValuativeExtension.mapValueGroupWithZero_valuation, ← fL.strictMono.lt_iff_lt]
            calc fL.emb (ValuativeExtension.mapValueGroupWithZero K L (valuation K k))
                < fL.emb (ValuativeExtension.mapValueGroupWithZero K L (c ^ n)) :=
                  fL.strictMono (ValuativeExtension.mapValueGroupWithZero_strictMono hk)
              _ = (fL.emb (ValuativeExtension.mapValueGroupWithZero K L c)) ^ n := by
                  rw [map_pow, map_pow]
              _ < fL.emb (γ : ValueGroupWithZero L) := hn
          constructor
          simp_rw [Algebra.smul_def]
          exact (halg.comp continuous_fst).mul continuous_snd
        haveI : IsModuleTopology K L := isModuleTopologyOfFiniteDimensional (𝕜 := K) (E := L)
        exact eq_moduleTopology K L
      rw [h_given, h_v]
    -- Transport `IsValuativeTopology` across the topology equality.
    apply IsValuativeTopology.of_zero
    intro s
    have hnhds : 𝓝 (0 : L) = @nhds L (ValuativeRel.topologicalSpace L) 0 :=
      congrArg (fun t => @nhds L t 0) hEq
    rw [hnhds]
    exact @IsValuativeTopology.mem_nhds_zero_iff L _ _ (ValuativeRel.topologicalSpace L)
      (ValuativeRel.isValuativeTopology L) s
  exact ⟨⟩

end Task2
