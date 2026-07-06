module

public import Mathlib.RingTheory.SimpleRing.Basic

@[expose] public section

universe u

variable (A : Type u) [Ring A]

open TwoSidedIdeal

lemma IsSimpleRing.iff_eq_zero_or_injective [Nontrivial A] :
    IsSimpleRing A ↔ ∀ ⦃B : Type u⦄ [Ring B] (f : A →+* B),
    TwoSidedIdeal.ker f = ⊤ ∨ Function.Injective f := by
  refine ⟨fun hA B _ f ↦ ?_, ?_⟩
  · rcases hA.injective_ringHom_or_subsingleton_codomain f with h' | h'
    · tauto
    · refine Or.inl (eq_top_iff.2 <| le_iff.2 fun x _ => ?_)
      simp [TwoSidedIdeal.mem_ker, Subsingleton.elim (f x) 0]
  · refine fun h ↦ ⟨⟨fun I ↦ ?_⟩⟩
    rcases h I.ringCon.mk' with h | h
    · refine Or.inr <| eq_top_iff.2 <| le_iff.2 fun x hx ↦ ?_
      simpa [← h] using hx
    · exact Or.inl <| by simpa using TwoSidedIdeal.ker_eq_bot _|>.2 h

lemma IsSimpleRing.iff_eq_zero_or_injective'
    (k : Type*) [CommRing k] [Algebra k A] [Nontrivial A] :
    IsSimpleRing A ↔
    ∀ ⦃B : Type u⦄ [Ring B] [Algebra k B] (f : A →ₐ[k] B),
      TwoSidedIdeal.ker f = ⊤ ∨ Function.Injective f := by
  refine ⟨fun hA B _ _ f ↦ (IsSimpleRing.iff_eq_zero_or_injective A).1 hA f.toRingHom, fun h ↦ ?_⟩
  refine ⟨⟨fun I ↦ ?_⟩⟩
  let f : A →ₐ[k] I.ringCon.Quotient := { I.ringCon.mk' with commutes' _ := rfl }
  have hker : TwoSidedIdeal.ker f = TwoSidedIdeal.ker I.ringCon.mk' := rfl
  rcases h f with h | h
  · rw [hker] at h
    refine Or.inr <| eq_top_iff.2 <| le_iff.2 fun x hx ↦ ?_
    simpa [← h] using hx
  · rw [← ker_eq_bot, hker] at h
    exact Or.inl <| by simpa using h
