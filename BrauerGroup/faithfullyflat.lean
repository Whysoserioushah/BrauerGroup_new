import BrauerGroup.CentralSimple

universe u

class Module.FaithfullyFlat (R : Type u) (M : Type u)
    [CommRing R] [AddCommGroup M] [Module R M] : Prop where
  out :
    ∀ (N₁ N₂ N₃ : Type u) [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃]
    [Module R N₁] [Module R N₂] [Module R N₃] (l₁₂ : N₁ →ₗ[R] N₂) (l₂₃ : N₂ →ₗ[R] N₃),
    Function.Exact l₁₂ l₂₃ ↔
    Function.Exact (l₁₂.lTensor M) (l₂₃.lTensor M)

lemma Module.FaithfullyFlat.rTensor (R : Type u) (M : Type u)
    [CommRing R] [AddCommGroup M] [Module R M] [h : Module.FaithfullyFlat R M]
    (N₁ N₂ N₃ : Type u) [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃]
    [Module R N₁] [Module R N₂] [Module R N₃]
    (l₁₂ : N₁ →ₗ[R] N₂) (l₂₃ : N₂ →ₗ[R] N₃) :
    Function.Exact l₁₂ l₂₃ ↔
    Function.Exact (l₁₂.rTensor M) (l₂₃.rTensor M) := by
  rw [h.1]
  fapply Function.Exact.iff_of_ladder_linearEquiv
    (e₁ := TensorProduct.comm _ _ _)
    (e₂ := TensorProduct.comm _ _ _)
    (e₃ := TensorProduct.comm _ _ _)
  · ext; simp
  · ext; simp

instance (R : Type*) [CommRing R] : Module.FaithfullyFlat R R := by
  constructor
  intro N₁ N₂ N₃ _ _ _ _ _ _ f g
  fapply Function.Exact.iff_of_ladder_linearEquiv (e₁ := TensorProduct.lid _ _)
    (e₂ := TensorProduct.lid _ _) (e₃ := TensorProduct.lid _ _)
  · ext n; simp
  · ext n; simp

open DirectSum TensorProduct

lemma TensorProduct.puretensor_repr (R M N: Type u) [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]: ∀(x : M ⊗[R] N), ∃(I : Finset (M ⊗[R] N)) (m : M ⊗[R] N → M)
    (n : M ⊗[R] N → N), x = ∑ i in I, m i ⊗ₜ n i := fun x => by
  classical
  have mem1 : x ∈ (⊤ : Submodule R _) := ⟨⟩
  rw [← TensorProduct.span_tmul_eq_top, mem_span_set] at mem1
  obtain ⟨r, hr, (eq1 : ∑ i in r.support, (_ • _) = _)⟩ := mem1
  choose a a' haa' using hr
  replace eq1 := calc _
    x = ∑ i in r.support, r i • i := eq1.symm
    _ = ∑ i in r.support.attach, (r i : R) • (i : (M ⊗[R] N))
      := Finset.sum_attach _ _ |>.symm
    _ = ∑ i in r.support.attach, (r i • a i.2 ⊗ₜ[R] a' i.2) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [haa' i.2]
    _ = ∑ i in r.support.attach, ((r i • a i.2) ⊗ₜ[R] a' i.2) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [TensorProduct.smul_tmul']
  use r.support
  use fun i => if h : i ∈ r.support then r i • a h else 0
  use fun i => if h : i ∈ r.support then a' h else 0
  rw [eq1] ; conv_rhs => rw [← Finset.sum_attach]
  refine Finset.sum_congr rfl fun _ _ ↦ (by split_ifs with h <;> aesop)

noncomputable def QuotientTensorEquiv_toFun (M R L: Type u) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup L]
    [Module R L] (N : Submodule R M) :
    (M ⧸ N) ⊗[R] L →ₗ[R] (M ⊗[R] L)⧸ (LinearMap.range <| N.subtype.rTensor L) :=
  TensorProduct.lift  <|
    Submodule.liftQ _ {
      toFun := fun m =>
      { toFun := fun l => Submodule.Quotient.mk <| m ⊗ₜ[R] l
        map_add' := by intros; simp [tmul_add]
        map_smul' := by intros; simp }
      map_add' := by intros; ext; simp [add_tmul]
      map_smul' := by intros; ext; simp [smul_tmul]
    } fun n hn => by
      simp only [LinearMap.mem_ker, LinearMap.coe_mk, AddHom.coe_mk]
      ext l
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply,
        Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
      exact ⟨⟨n, hn⟩ ⊗ₜ l, rfl⟩

noncomputable def QuotientTensorEquiv_invFun (M R L: Type u) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup L]
    [Module R L] (N : Submodule R M) :
    (M ⊗[R] L)⧸ (LinearMap.range <| N.subtype.rTensor L) →ₗ[R] (M ⧸ N) ⊗[R] L :=
  Submodule.liftQ _ (TensorProduct.lift {
    toFun := fun m => {
      toFun := fun l => (Submodule.Quotient.mk m) ⊗ₜ[R] l
      map_add' := by intros; simp [tmul_add]
      map_smul' := by intros; simp
    }
    map_add' := by intros; ext; simp [add_tmul]
    map_smul' := by intros; ext; simp [smul_tmul]
  })  <| by
    rintro _ ⟨x, rfl⟩
    simp only [LinearMap.mem_ker]
    obtain ⟨i, s, t, rfl⟩ := TensorProduct.puretensor_repr (x := x)
    simp only [map_sum, LinearMap.rTensor_tmul, Submodule.coeSubtype, lift.tmul, LinearMap.coe_mk,
      AddHom.coe_mk]
    apply Finset.sum_eq_zero
    intros x _
    rw [show Submodule.Quotient.mk (s x).1 = (0 : M ⧸ N) by simp only [Submodule.Quotient.mk_eq_zero,
      SetLike.coe_mem], zero_tmul]

noncomputable def QuotientTensorEquiv (M R L: Type u) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup L]
    [Module R L] (N : Submodule R M) :
    (M ⧸ N) ⊗[R] L ≃ₗ[R] (M ⊗[R] L)⧸ (LinearMap.range <| N.subtype.rTensor L) :=
  LinearEquiv.ofLinear (QuotientTensorEquiv_toFun _ _ _ _) (QuotientTensorEquiv_invFun _ _ _ _) (by
    ext ; simp only [QuotientTensorEquiv_toFun, QuotientTensorEquiv_invFun,
      AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
      LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Submodule.liftQ_apply,
      lift.tmul, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_comp] )
    (by ext; simp [QuotientTensorEquiv_toFun, QuotientTensorEquiv_invFun])

lemma Module.FaithfullyFlat.flat
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    [fl : Module.FaithfullyFlat R M] :
    Module.Flat R M := by
  rw [Module.Flat.iff_lTensor_exact]
  intro N₁ N₂ N₃ _ _ _ _ _ _ l12 l23
  exact fl.1 N₁ N₂ N₃ l12 l23 |>.1

lemma Module.FaithfullyFlat.faithful
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    [fl : Module.FaithfullyFlat R M] :
    ∀ (N : Type u) [AddCommGroup N] [Module R N], Nontrivial N → Nontrivial (M ⊗[R] N) := by
  intro N _ _ hN
  by_contra! hMN
  have := subsingleton_or_nontrivial (M ⊗[R] N)
  simp only [hMN, or_false] at this
  have : (⊤ : Submodule R (M ⊗[R] N)) = 0 := Subsingleton.eq_zero ⊤
  have hM' := fl.1 (0 : Submodule R N) N (0 : Submodule R N) 0 0 |>.2 (by
      rw [LinearMap.exact_iff]
      simp only [Submodule.zero_eq_bot, LinearMap.lTensor_zero, LinearMap.ker_zero,
        LinearMap.range_zero, this] )
  rw [LinearMap.exact_iff] at hM'
  simp only [Submodule.zero_eq_bot, LinearMap.ker_zero, LinearMap.range_zero, top_ne_bot] at hM'

lemma Module.FaithfullyFlat.of_flat_and_faithful_aux1
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    [ft : Module.Flat R M]
    (N₁ N₂ N₃ : Type u) [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃]
    [Module R N₁] [Module R N₂] [Module R N₃] (l12 : N₁ →ₗ[R] N₂) (l23 : N₂ →ₗ[R] N₃)
    (ex : Function.Exact l12 l23) :
    Function.Exact (LinearMap.lTensor M l12) (LinearMap.lTensor M l23) := by
  rw [Module.Flat.iff_lTensor_exact] at ft
  apply ft
  assumption

lemma Module.FaithfullyFlat.of_flat_and_faithful_aux2
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    [ft : Module.Flat R M]
    (faithful : ∀ (N : Type u) [AddCommGroup N] [Module R N], Nontrivial N → Nontrivial (M ⊗[R] N))
    {N₁ N₂ N₃ : Type u} [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃]
    [Module R N₁] [Module R N₂] [Module R N₃] (l12 : N₁ →ₗ[R] N₂) (l23 : N₂ →ₗ[R] N₃)
    (ex : Function.Exact (LinearMap.lTensor M l12) (LinearMap.lTensor M l23)) :
    (LinearMap.range l12) ≤ (LinearMap.ker l23) := by
  classical
  intro x hx
  simp only [LinearMap.mem_ker]
  obtain ⟨y, hy⟩ := hx
  -- have := Function.Exact.linearMap_comp_eq_zero hlt'
  have : ∀ (n1 : N₁) (m : M), LinearMap.lTensor M l23
    (LinearMap.lTensor M l12 (m ⊗ₜ n1)) = 0 := fun n1 m ↦ by
    exact Function.Exact.apply_apply_eq_zero ex (m ⊗ₜ[R] n1)
  simp only [LinearMap.lTensor_tmul] at this
  have eq1 := this y
  by_contra! hxx
  let E : Submodule R N₃ := Submodule.span R {l23 x}
  have hE : Nontrivial E := ⟨0, ⟨⟨l23 x, Submodule.mem_span_singleton_self _⟩,
    Subtype.coe_ne_coe.1 hxx.symm⟩⟩
  haveI : Nontrivial (M ⊗[R] E) := faithful E hE
  have hEE : ∀ (xx : M ⊗[R] E), ∃ (I : Finset (M ⊗[R] E)) (mm : M ⊗[R] E → M),
    xx = ∑ i in I, (mm i) ⊗ₜ ⟨l23 x, Submodule.mem_span_singleton_self _⟩ := fun xx ↦ by
    obtain ⟨I, mmm, hmmm, heqeq⟩ := TensorProduct.puretensor_repr R M E xx
    use I
    have : ∃(rr : M ⊗[R] E → R), ∀ i ∈ I, hmmm i = rr i •
      ⟨l23 x, Submodule.mem_span_singleton_self _⟩ := by
      use fun i => if i ∈ I then (Submodule.mem_span_singleton.1 (hmmm i).2).choose else 0
      intro i hi
      simp only [ite_smul, SetLike.mk_smul_mk, zero_smul]
      split_ifs
      · exact SetCoe.ext $ Submodule.mem_span_singleton.1 (hmmm i).2|>.choose_spec.symm
      · tauto
    obtain ⟨rr, hrr⟩ := this
    use fun i => rr i • mmm i
    replace heqeq := calc _
      xx = ∑ i ∈ I, mmm i ⊗ₜ[R] hmmm i := heqeq
      _ = ∑ i ∈ I, mmm i ⊗ₜ (rr i • ⟨l23 x, Submodule.mem_span_singleton_self _⟩) :=
        Finset.sum_congr rfl fun i hi ↦ by rw [hrr i] ; exact hi
    simp_rw [TensorProduct.tmul_smul] at heqeq
    exact heqeq
  rw [hy] at eq1
  have eq0: (⊤ : Submodule R (M ⊗[R] E)) = 0 := by
    ext xx
    refine ⟨fun _ ↦ ?_, fun _ ↦ ⟨⟩⟩
    obtain ⟨I, mm, heqx⟩ := hEE xx
    simp only [Submodule.zero_eq_bot, Submodule.mem_bot]
    replace heqx := calc _
      xx = ∑ i ∈ I, mm i ⊗ₜ ⟨l23 x, Submodule.mem_span_singleton_self _⟩ := heqx
      _ = ∑ _ ∈ I, (0 : M ⊗[R] E) := Finset.sum_congr rfl fun i _ ↦
        (by
          apply_fun (LinearMap.lTensor (M := M) E.subtype) using
            (Module.Flat.lTensor_preserves_injective_linearMap (M := M) E.subtype $
              Submodule.injective_subtype E)
          simp only [LinearMap.lTensor_tmul, Submodule.coeSubtype, eq1, map_zero])
    simp only [Finset.sum_const_zero] at heqx
    exact heqx
  have hEEE : (⊤ : Submodule R (M ⊗[R] E)) ≠ 0 := Submodule.nontrivial_iff_ne_bot.1
    (by simp_all only [implies_true, ne_eq, Submodule.zero_eq_bot, top_ne_bot, E])
  tauto

noncomputable
def Module.FaithfullyFlat.of_flat_and_faithful.equiv'InnerForward
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    (N₂ N₃ : Type u) [AddCommGroup N₂] [AddCommGroup N₃]
    [Module R N₂] [Module R N₃] (l23 : N₂ →ₗ[R] N₃) :
    (LinearMap.ker l23) ⊗[R] M →ₗ[R] (LinearMap.ker (LinearMap.rTensor M l23)) :=
  TensorProduct.lift
    { toFun := fun x =>
      { toFun := fun m => ⟨x ⊗ₜ m, by simp only [LinearMap.mem_ker,
        LinearMap.rTensor_tmul, LinearMap.map_coe_ker, zero_tmul]⟩
        map_add' := fun m1 m2 => by simp only [tmul_add, AddSubmonoid.mk_add_mk]
        map_smul' := fun r m => by
          simp only [tmul_smul, RingHom.id_apply, SetLike.mk_smul_mk]}
      map_add' := fun x y => by
        simp only [AddSubmonoid.coe_add, Submodule.coe_toAddSubmonoid, add_tmul]; rfl
      map_smul' := fun r x => by
        simp only [SetLike.val_smul, ← smul_tmul', RingHom.id_apply]; rfl }

noncomputable
def Module.FaithfullyFlat.of_flat_and_faithful.equiv'InnerBackwardInner
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    [ft : Module.Flat R M]
    (N₁ N₂ N₃ : Type u) [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃]
    [Module R N₁] [Module R N₂] [Module R N₃] (l12 : N₁ →ₗ[R] N₂) (l23 : N₂ →ₗ[R] N₃)
    (ex' : Function.Exact (LinearMap.rTensor M l12) (LinearMap.rTensor M l23)) :
    (LinearMap.range l12) ⊗[R] M  ≃ₗ[R]
    (LinearMap.range (LinearMap.rTensor M (LinearMap.range l12).subtype)) :=
  LinearEquiv.ofBijective
    (LinearMap.rangeRestrict <| LinearMap.rTensor M (LinearMap.range l12).subtype)
    ⟨by
      erw [Set.injective_codRestrict]
      rw [Module.Flat.iff_rTensor_preserves_injective_linearMap] at ft
      apply ft; exact Subtype.val_injective, LinearMap.surjective_rangeRestrict _⟩

noncomputable
def Module.FaithfullyFlat.of_flat_and_faithful.equiv'InnerBackward
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    [ft : Module.Flat R M]
    (N₁ N₂ N₃ : Type u) [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃]
    [Module R N₁] [Module R N₂] [Module R N₃] (l12 : N₁ →ₗ[R] N₂) (l23 : N₂ →ₗ[R] N₃)
    (ex' : Function.Exact (LinearMap.rTensor M l12) (LinearMap.rTensor M l23))
    (le1 : LinearMap.range l12 ≤ LinearMap.ker l23) :
    (LinearMap.ker (LinearMap.rTensor M l23)) →ₗ[R] (LinearMap.ker l23) ⊗[R] M :=
  (LinearMap.rTensor M <| Submodule.inclusion le1) ∘ₗ
      (Module.FaithfullyFlat.of_flat_and_faithful.equiv'InnerBackwardInner R M
        _ _ _ l12 l23 ex').symm ∘ₗ
      (Submodule.inclusion <| by
        rw [LinearMap.exact_iff] at ex'
        rw [← LinearMap.rTensor_range, ex'] :
        _ →ₗ[R] LinearMap.range (LinearMap.rTensor M (LinearMap.range l12).subtype))

lemma Module.FaithfullyFlat.of_flat_and_faithful.equiv'InnerBackwardInner_symm_apply
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    [ft : Module.Flat R M]
    (N₁ N₂ N₃ : Type u) [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃]
    [Module R N₁] [Module R N₂] [Module R N₃] (l12 : N₁ →ₗ[R] N₂) (l23 : N₂ →ₗ[R] N₃)
    (ex' : Function.Exact (LinearMap.rTensor M l12) (LinearMap.rTensor M l23))
    (y : (LinearMap.range l12) ⊗[R] M)
    (hy : (LinearMap.rTensor M (LinearMap.range l12).subtype) y ∈
      LinearMap.range (LinearMap.rTensor M (LinearMap.range l12).subtype)) :
    (equiv'InnerBackwardInner R M N₁ N₂ N₃ l12 l23 ex').symm
      ⟨(LinearMap.rTensor M (LinearMap.range l12).subtype) y, hy⟩ = y := by
  apply_fun (equiv'InnerBackwardInner R M N₁ N₂ N₃ l12 l23 ex') using LinearEquiv.injective _
  simp only [LinearEquiv.apply_symm_apply]
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    simp only [LinearMap.rTensor_tmul, Submodule.coeSubtype, equiv'InnerBackwardInner,
      LinearEquiv.ofBijective_apply]
    ext
    simp [LinearMap.rangeRestrict, LinearMap.codRestrict_apply]
  | add a b ha hb =>
    simp only [LinearMap.mem_range, exists_apply_eq_apply, forall_true_left] at ha hb
    conv_rhs => rw [map_add]
    rw [← ha, ← hb]
    ext : 1
    simp only [map_add, Submodule.mem_toAddSubmonoid, LinearMap.mem_range, exists_apply_eq_apply,
      AddSubmonoid.mk_add_mk]

lemma Module.FaithfullyFlat.of_flat_and_faithful.equiv'Inner_comp
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    [ft : Module.Flat R M]
    (N₁ N₂ N₃ : Type u) [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃]
    [Module R N₁] [Module R N₂] [Module R N₃] (l12 : N₁ →ₗ[R] N₂) (l23 : N₂ →ₗ[R] N₃)
    (ex' : Function.Exact (LinearMap.rTensor M l12) (LinearMap.rTensor M l23))
    (le1 : LinearMap.range l12 ≤ LinearMap.ker l23) :
    equiv'InnerForward R M N₂ N₃ l23 ∘ₗ
      equiv'InnerBackward R M N₁ N₂ N₃ l12 l23 ex' le1 =
    LinearMap.id := by
  ext ⟨x, hx⟩
  rw [LinearMap.exact_iff.1 ex'] at hx
  obtain ⟨x, rfl⟩ := hx
  have := LinearMap.exact_iff.1 ex' ▸ hx

  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
  dsimp [equiv'InnerBackward]
  rw [Submodule.inclusion_apply]
  simp only
  generalize_proofs _ _ _ _ _ _ h
  obtain ⟨y, hy⟩ := h
  simp_rw [← hy]
  rw [Module.FaithfullyFlat.of_flat_and_faithful.equiv'InnerBackwardInner_symm_apply]
  clear hy
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    simp [equiv'InnerForward]
  | add a b ha hb =>
    simp [map_add, ha, hb]

lemma Module.FaithfullyFlat.of_flat_and_faithful.equiv'Inner_comp'
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    [ft : Module.Flat R M]
    (N₁ N₂ N₃ : Type u) [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃]
    [Module R N₁] [Module R N₂] [Module R N₃] (l12 : N₁ →ₗ[R] N₂) (l23 : N₂ →ₗ[R] N₃)
    (ex' : Function.Exact (LinearMap.rTensor M l12) (LinearMap.rTensor M l23))
    (le1 : LinearMap.range l12 ≤ LinearMap.ker l23) :
    equiv'InnerBackward R M N₁ N₂ N₃ l12 l23 ex' le1 ∘ₗ equiv'InnerForward R M N₂ N₃ l23  =
    LinearMap.id := by
  ext ⟨a, ha⟩ m
  simp only [equiv'InnerBackward, equiv'InnerForward, AlgebraTensorModule.curry_apply, curry_apply,
    LinearMap.coe_restrictScalars, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    lift.tmul, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_coe, id_eq]
  rw [Submodule.inclusion_apply]
  simp only
  generalize_proofs _ _ _ _ _ h
  obtain ⟨y, hy⟩ := h
  simp_rw [← hy]
  rw [Module.FaithfullyFlat.of_flat_and_faithful.equiv'InnerBackwardInner_symm_apply]
  rw [show (⟨a, ha⟩ ⊗ₜ[R] m : (LinearMap.ker l23) ⊗[R] M) =
    (LinearMap.rTensor M <| Submodule.inclusion le1) y by
    apply_fun LinearMap.rTensor M (Submodule.subtype _)
    · simp only [LinearMap.rTensor_tmul, Submodule.coeSubtype, ← hy]
      rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
      congr 1
    · apply Module.Flat.rTensor_preserves_injective_linearMap
      exact Subtype.val_injective]

noncomputable
def Module.FaithfullyFlat.of_flat_and_faithful.equiv'Inner
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Flat R M]
    (N₁ N₂ N₃ : Type u) [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃]
    [Module R N₁] [Module R N₂] [Module R N₃] (l12 : N₁ →ₗ[R] N₂) (l23 : N₂ →ₗ[R] N₃)
    (ex' : Function.Exact (LinearMap.rTensor M l12) (LinearMap.rTensor M l23))
    (le1 : LinearMap.range l12 ≤ LinearMap.ker l23) :
    (LinearMap.ker l23) ⊗[R] M ≃ₗ[R] (LinearMap.ker (LinearMap.rTensor M l23)) :=


  LinearEquiv.ofLinear
    (Module.FaithfullyFlat.of_flat_and_faithful.equiv'InnerForward R M _ _ l23)
    (Module.FaithfullyFlat.of_flat_and_faithful.equiv'InnerBackward R M _ _ _
      l12 l23 ex' le1)
    (Module.FaithfullyFlat.of_flat_and_faithful.equiv'Inner_comp R M _ _ _ l12 l23 ex' le1)

    (Module.FaithfullyFlat.of_flat_and_faithful.equiv'Inner_comp' R M _ _ _ l12 l23 ex' le1)

noncomputable
def Module.FaithfullyFlat.of_flat_and_faithful.equiv'
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    [ft : Module.Flat R M]
    (faithful : ∀ (N : Type u) [AddCommGroup N] [Module R N], Nontrivial N → Nontrivial (M ⊗[R] N))
    (N₁ N₂ N₃ : Type u) [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃]
    [Module R N₁] [Module R N₂] [Module R N₃] (l12 : N₁ →ₗ[R] N₂) (l23 : N₂ →ₗ[R] N₃)
    (ex : Function.Exact (LinearMap.lTensor M l12) (LinearMap.lTensor M l23))
    (ex' : Function.Exact (LinearMap.rTensor M l12) (LinearMap.rTensor M l23))
    (le1 : LinearMap.range l12 ≤ LinearMap.ker l23) :
    (((LinearMap.ker l23) ⊗[R] M) ⧸
      LinearMap.range ((LinearMap.range (Submodule.inclusion <|
        Module.FaithfullyFlat.of_flat_and_faithful_aux2 R M faithful l12 l23 ex)).subtype.rTensor M)) ≃ₗ[R]
    (LinearMap.ker (l23.rTensor M) ⧸
      LinearMap.range
        (Submodule.inclusion (p := LinearMap.range (l12.rTensor M))
          (p' := LinearMap.ker (l23.rTensor M)) <| by rw [LinearMap.exact_iff] at ex'; rw [ex'])) :=
  Submodule.Quotient.equiv _ _
    (Module.FaithfullyFlat.of_flat_and_faithful.equiv'Inner R M _ _ _ l12 l23 ex' le1) <| by
    erw [Submodule.map_equiv_eq_comap_symm]
    ext ⟨x, hx⟩; constructor
    · intro H
      simp only [LinearMap.mem_ker, LinearEquiv.ofLinear_symm_toLinearMap, Submodule.mem_comap,
        LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearMap.mem_range,
        Subtype.exists] at H ⊢
      rw [LinearMap.exact_iff] at ex'
      rw [ex'] at hx
      obtain ⟨x, rfl⟩ := hx
      refine ⟨_, ⟨x, rfl⟩, ?_⟩
      ext
      simp only [Submodule.coe_inclusion]
    · rw [LinearMap.exact_iff] at ex'
      rw [ex'] at hx
      obtain ⟨x, rfl⟩ := hx
      rintro -
      revert hx
      simp_rw [ex']
      simp only [LinearMap.mem_range, exists_apply_eq_apply,
        LinearEquiv.ofLinear_symm_toLinearMap, Submodule.mem_comap, LinearMap.coe_comp,
        LinearEquiv.coe_coe, Function.comp_apply, forall_true_left]
      induction x using TensorProduct.induction_on with
      | zero =>
        refine ⟨0, by simp only [map_zero]; symm; erw [map_zero]⟩
      | tmul a m =>
        refine ⟨⟨⟨l12 a, le1 <| by simp only [LinearMap.mem_range, exists_apply_eq_apply]⟩,
          by simpa only [LinearMap.mem_range, Subtype.exists] using ⟨l12 a, ⟨_, rfl⟩, rfl⟩⟩ ⊗ₜ[R] m,
          ?_⟩
        simp only [LinearMap.rTensor_tmul, Submodule.coeSubtype, equiv'Inner, equiv'InnerBackward,
          LinearEquiv.ofLinear_symm_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
          Function.comp_apply]
        rw [Submodule.inclusion_apply]
        simp only
        generalize_proofs _ h1 _ _ _ _ h2
        obtain ⟨y, hy⟩ := h2
        simp_rw [← hy]
        rw [equiv'InnerBackwardInner_symm_apply]
        apply_fun (LinearMap.ker l23).subtype.rTensor M
        · simp only [LinearMap.rTensor_tmul, Submodule.coeSubtype, ← hy];
          rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
          rfl
        rw [Module.Flat.iff_rTensor_preserves_injective_linearMap] at ft
        apply ft
        exact Subtype.val_injective
      | add x y hx hy =>
        obtain ⟨X, hX⟩ := hx
        obtain ⟨Y, hY⟩ := hy
        refine ⟨X + Y, ?_⟩
        rw [map_add, hX, hY, ← map_add]
        congr 1
        ext : 2
        simp only [AddSubmonoid.mk_add_mk, map_add]

lemma Module.FaithfullyFlat.iff_flat_and_faithful
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M] :
    Module.FaithfullyFlat R M ↔
    Module.Flat R M ∧
    (∀ (N : Type u) [AddCommGroup N] [Module R N], Nontrivial N → Nontrivial (M ⊗[R] N)) := by
  classical
  constructor
  · intro hM
    refine ⟨Module.FaithfullyFlat.flat _ _, Module.FaithfullyFlat.faithful _ _⟩
  · rintro ⟨hM, hN⟩
    refine ⟨fun N₁ N₂ N₃ _ _ _ _ _ _ l12 l23 ↦
      ⟨Module.FaithfullyFlat.of_flat_and_faithful_aux1 _ _ _ _ _ _ _, fun hlt ↦ ?_⟩⟩

    · rw [LinearMap.exact_iff]
      have le1 := Module.FaithfullyFlat.of_flat_and_faithful_aux2 R M hN _ _ hlt
      refine le_antisymm ?_ le1
      have hlt' : Function.Exact (LinearMap.rTensor M l12) (LinearMap.rTensor M l23) := by
        fapply hlt.of_ladder_linearEquiv_of_exact (e₁ := TensorProduct.comm _ _ _)
          (e₂ := TensorProduct.comm _ _ _) (e₃ := TensorProduct.comm _ _ _)
        · ext
          simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
            LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, comm_tmul,
            LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
        · ext
          simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
            LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, comm_tmul,
            LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]

      let equiv := QuotientTensorEquiv (LinearMap.ker l23) R M <| LinearMap.range
        (Submodule.inclusion le1)

      let equiv' : (((LinearMap.ker l23) ⊗[R] M) ⧸
            LinearMap.range ((LinearMap.range (Submodule.inclusion le1)).subtype.rTensor M)) ≃ₗ[R]
            (LinearMap.ker (l23.rTensor M) ⧸
              LinearMap.range
                (Submodule.inclusion (p := LinearMap.range (l12.rTensor M))
                  (p' := LinearMap.ker (l23.rTensor M)) <| by
                  rw [LinearMap.exact_iff] at hlt'
                  rw [hlt'])) :=
        Module.FaithfullyFlat.of_flat_and_faithful.equiv' R M hN _ _ _ l12 l23 hlt hlt' le1



      haveI h1 : Subsingleton
        ((LinearMap.ker l23) ⊗[R] M ⧸
          LinearMap.range ((LinearMap.range (Submodule.inclusion le1)).subtype.rTensor M)) := by
        refine @Function.Surjective.subsingleton (f := equiv'.symm) ?_ equiv'.symm.surjective
        rw [Submodule.subsingleton_quotient_iff_eq_top, Submodule.range_inclusion,
          Submodule.comap_subtype_eq_top]
        rw [LinearMap.exact_iff] at hlt'
        rw [hlt']
      haveI h2 : Subsingleton
        (LinearMap.ker l23 ⧸ (LinearMap.range (Submodule.inclusion le1))) := by
        refine subsingleton_or_nontrivial _ |>.resolve_right fun H => ?_
        specialize hN _ H
        obtain ⟨x, hx⟩ := nontrivial_iff_exists_ne 0 |>.1 hN
        have hx' : (equiv <| TensorProduct.comm _ _ _ x) ≠ 0 := by simpa
        rw [subsingleton_iff_forall_eq 0] at h1
        exact hx' <| h1 (equiv <| TensorProduct.comm _ _ _ x)


      intro x hx
      have := h2.elim (Submodule.Quotient.mk ⟨x, hx⟩) 0
      simp only [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range, Subtype.exists] at this
      obtain ⟨_, ⟨y, rfl⟩, hy⟩ := this
      refine ⟨y, Subtype.ext_iff.1 hy⟩


open TensorProduct in
instance Module.FaithfullyFlat.directSum (ι : Type u) (R : Type u) [CommRing R]
    (M : ι → Type u) [Nonempty ι] [DecidableEq ι]
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [faithfully_flat : ∀ i, Module.FaithfullyFlat R (M i)] :
    Module.FaithfullyFlat R (⨁ i : ι, M i) := by
  rw [Module.FaithfullyFlat.iff_flat_and_faithful]
  haveI : ∀ i, Module.Flat R (M i) := by
    intro i
    rw [Module.Flat.iff_lTensor_exact]
    intros N₁ N₂ N₃ _ _ _ _ _ _ f g H
    exact faithfully_flat i |>.out N₁ N₂ N₃ f g |>.1 H

  refine ⟨inferInstance, fun N _ _ _ => ?_⟩
  let e := TensorProduct.directSumLeft R (fun i => M i) N
  haveI nt : ∀ i, Nontrivial (M i ⊗[R] N) := by
    intro i
    have := faithfully_flat i
    rw [Module.FaithfullyFlat.iff_flat_and_faithful] at this
    exact this.2 N inferInstance

  -- have : Nonempty ι := sorry
  haveI : Nontrivial (⨁ (i : ι), M i ⊗[R] N) := by
    let i : ι := Nonempty.some inferInstance
    obtain ⟨m, n, h⟩ := nt i
    refine ⟨.of _ i m, .of _ i n, ?_⟩
    contrapose! h
    classical
    replace h := DFunLike.ext_iff.1 h i
    rw [DirectSum.of_apply, DirectSum.of_apply, dif_pos rfl, dif_pos rfl] at h
    exact h
  exact Function.Surjective.nontrivial (LinearEquiv.surjective e)

lemma Module.FaithfullyFlat.congr {R : Type u} {M : Type u} {N : Type u}
    [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [h : Module.FaithfullyFlat.{u} R M]
    (e : M ≃ₗ[R] N) : Module.FaithfullyFlat.{u} R N := by
  constructor
  intro N₁ N₂ N₃ _ _ _ _ _ _ f g
  rw [h.1]
  fapply Function.Exact.iff_of_ladder_linearEquiv
    (e₁ := TensorProduct.congr e.symm (LinearEquiv.refl _ _))
    (e₂ := TensorProduct.congr e.symm (LinearEquiv.refl _ _))
    (e₃ := TensorProduct.congr e.symm (LinearEquiv.refl _ _))
  · ext; simp
  · ext; simp

instance (R M : Type u) [Nontrivial M]
    [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M] :
    Module.FaithfullyFlat R M := by
  have i1 : Module.FaithfullyFlat R (Module.Free.ChooseBasisIndex R M →₀ R) := by
    haveI : Nonempty (Module.Free.ChooseBasisIndex R M) := by
      have h : IsEmpty (Module.Free.ChooseBasisIndex R M) ∨
        Nonempty (Module.Free.ChooseBasisIndex R M) := isEmpty_or_nonempty _
      refine h.resolve_left ?_
      intro h
      let e := (Module.Free.repr R M)
      have : Subsingleton (Module.Free.ChooseBasisIndex R M →₀ R) := inferInstance
      have : Subsingleton M := Function.Injective.subsingleton (LinearEquiv.injective e)
      rw [← not_nontrivial_iff_subsingleton] at this
      contradiction
    apply Module.FaithfullyFlat.congr (M := ⨁ _ : Module.Free.ChooseBasisIndex R M, R)
    exact (finsuppLEquivDirectSum R R (Module.Free.ChooseBasisIndex R M)).symm
  exact Module.FaithfullyFlat.congr (Module.Free.repr R M).symm

variable (K : Type u) [Field K]
open TensorProduct in
lemma IsSimpleRing.left_of_tensor (B C : Type u)
    [Ring B] [Ring C] [Algebra K C] [Algebra K B]
    [hbc : IsSimpleOrder (TwoSidedIdeal (B ⊗[K] C))] :
    IsSimpleOrder (TwoSidedIdeal B) := by
  have hB : Subsingleton B ∨ Nontrivial B := subsingleton_or_nontrivial B
  have hC : Subsingleton C ∨ Nontrivial C := subsingleton_or_nontrivial C
  rcases hB with hB|hB
  · have : Subsingleton (B ⊗[K] C) := by
      rw [← subsingleton_iff_zero_eq_one, show (0 : B ⊗[K] C) = 0 ⊗ₜ 0 by simp,
        show (1 : B ⊗[K] C) = 1 ⊗ₜ 1 by rfl, show (1 : B) = 0 from Subsingleton.elim _ _]
      simp only [tmul_zero, zero_tmul]
    have : Subsingleton (TwoSidedIdeal (B ⊗[K] C)) := by
      constructor
      intro I J
      refine SetLike.ext fun x => ?_
      rw [show x = 0 from Subsingleton.elim _ _]
      refine ⟨fun _ => TwoSidedIdeal.zero_mem _, fun _ => TwoSidedIdeal.zero_mem _⟩
    have H := hbc.1
    rw [← not_subsingleton_iff_nontrivial] at H
    contradiction

  rcases hC with hC|hC
  · have : Subsingleton (B ⊗[K] C) := by
      rw [← subsingleton_iff_zero_eq_one, show (0 : B ⊗[K] C) = 0 ⊗ₜ 0 by simp,
        show (1 : B ⊗[K] C) = 1 ⊗ₜ 1 by rfl, show (1 : C) = 0 from Subsingleton.elim _ _]
      simp only [tmul_zero, zero_tmul]
    have : Subsingleton (TwoSidedIdeal (B ⊗[K] C)) := by
      constructor
      intro I J
      refine SetLike.ext fun x => ?_
      rw [show x = 0 from Subsingleton.elim _ _]
      refine ⟨fun _ => TwoSidedIdeal.zero_mem _, fun _ => TwoSidedIdeal.zero_mem _⟩
    have H := hbc.1
    rw [← not_subsingleton_iff_nontrivial] at H
    contradiction

  by_contra h
  rw [TwoSidedIdeal.IsSimpleOrder.iff_eq_zero_or_injective' (k := K) (A := B)] at h
  push_neg at h
  obtain ⟨B', _, _, f, h1, h2⟩ := h
  have : Nontrivial B' := by
    contrapose! h1
    rw [← not_subsingleton_iff_nontrivial, not_not] at h1
    refine SetLike.ext ?_
    intro b
    simp only [TwoSidedIdeal.mem_ker]
    refine ⟨fun _ => trivial, fun _ => Subsingleton.elim _ _⟩
  let F : B ⊗[K] C →ₐ[K] (B' ⊗[K] C) := Algebra.TensorProduct.map f (AlgHom.id _ _)
  have hF := TwoSidedIdeal.IsSimpleOrder.iff_eq_zero_or_injective' (B ⊗[K] C) K |>.1 inferInstance F

  rcases hF with hF|hF
  · have : Nontrivial (B' ⊗[K] C) := by
      rw [← rank_pos_iff_nontrivial (R := K), rank_tensorProduct]
      simp only [gt_iff_lt, CanonicallyOrderedCommSemiring.mul_pos, Cardinal.zero_lt_lift_iff]
      rw [rank_pos_iff_nontrivial, rank_pos_iff_nontrivial]
      aesop
    have : 1 ∈ TwoSidedIdeal.ker F := by rw [hF]; trivial
    simp only [TwoSidedIdeal.mem_ker, _root_.map_one, one_ne_zero] at this
  · have h : Module.FaithfullyFlat K C := inferInstance
    have : Function.Exact (0 : PUnit.{u + 1} →ₗ[K] _) F := by
      intro x
      simp only [Set.mem_range, LinearMap.zero_apply, exists_const]
      rw [← show F 0 = 0 by simp, @Eq.comm _ 0 x]
      constructor
      · apply hF
      · rintro rfl; simp

    have : Function.Exact (0 : PUnit.{u + 1} →ₗ[K] _) f := by
      refine Module.FaithfullyFlat.rTensor (h := h) (l₁₂ := (0 : PUnit →ₗ[K] _) )
        (l₂₃ := f.toLinearMap) |>.2 ?_
      intro x
      change F x = 0 ↔ _
      aesop

    refine h2 fun x y hxy => ?_
    specialize this (x - y)
    simp only [map_sub, sub_eq_zero, Set.mem_range, LinearMap.zero_apply, exists_const] at this
    simpa [Eq.comm, sub_eq_zero] using this.1 hxy

open TensorProduct in
lemma IsSimpleRing.right_of_tensor (B C : Type u)
    [Ring B] [Ring C] [Algebra K C] [Algebra K B]
    [hbc : IsSimpleOrder (TwoSidedIdeal (B ⊗[K] C))] :
    IsSimpleOrder (TwoSidedIdeal C) := by
  haveI : IsSimpleOrder (TwoSidedIdeal (C ⊗[K] B)) := by
    let e : C ⊗[K] B ≃ₐ[K] (B ⊗[K] C) := Algebra.TensorProduct.comm _ _ _
    have := TwoSidedIdeal.orderIsoOfRingEquiv e.toRingEquiv
    exact (OrderIso.isSimpleOrder_iff this).mpr hbc
  apply IsSimpleRing.left_of_tensor (K := K) (B := C) (C := B)
