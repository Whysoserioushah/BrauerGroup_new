module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
## Results about two-sided ideals

-/

@[expose] public section

namespace TwoSidedIdeal

section NonUnitalNonAssoc

variable {R S F : Type*} [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S] [FunLike F R S]

lemma mem_image_of_mem_map_of_surjective [NonUnitalRingHomClass F R S] {f : F}
    (hf : Function.Surjective f) {I : TwoSidedIdeal R} {y} (H : y ∈ I.map f) :
    y ∈ f '' I :=
  span_induction (hx := H) (fun _ ↦ id) ⟨0, by simp⟩
    (fun _ _ _ _ ⟨a, ha, ha'⟩ ⟨b, hb, hb'⟩ ↦ ⟨a + b, I.add_mem ha hb, ha' ▸ hb' ▸ map_add ..⟩)
    (fun _ _ ⟨a, ha, ha'⟩ ↦ ⟨-a, I.neg_mem ha, ha' ▸ map_neg ..⟩)
    (fun c _ _ ⟨a, ha, ha'⟩ ↦
      let ⟨d, hd⟩ := hf c
      ⟨d * a, I.mul_mem_left _ _ ha, hd ▸ ha' ▸ map_mul ..⟩) <|
    fun b _ _ ⟨a, ha, ha'⟩ ↦
      let ⟨d, hd⟩ := hf b
      ⟨a * d, I.mul_mem_right _ _ ha, ha' ▸ hd ▸ map_mul ..⟩

lemma comap_coe {f : F} [NonUnitalRingHomClass F R S] (I : TwoSidedIdeal S) :
    I.comap f = f ⁻¹' I := by ext; simp [mem_comap]

lemma map_le_iff_le_comap {f : F} [NonUnitalRingHomClass F R S] (I : TwoSidedIdeal R)
    (J : TwoSidedIdeal S) : I.map f ≤ J ↔ I ≤ J.comap f :=
  span_le.trans <| Set.image_subset_iff.trans <|
    (J.comap_coe (f := f)).symm ▸ SetLike.coe_subset_coe

@[simp]
lemma span_eq_bot {s : Set R} :
    span s = ⊥ ↔ ∀ x ∈ s, x = 0 := _root_.eq_bot_iff.trans
  ⟨fun H _ h => (mem_bot R).mp <| H <| subset_span h,
   fun H => span_le.mpr fun x h => (mem_bot R).mpr <| H x h⟩

lemma span_singleton_eq_bot {x : R} :
    span ({x} : Set R) = ⊥ ↔ x = 0 := by simp

@[simp]
lemma map_bot [ZeroHomClass F R S] {f : F} :
    (⊥ : TwoSidedIdeal R).map f = ⊥ := by
  ext x
  simp [map, span_singleton_eq_bot.2]

protected theorem mem_map_of_mem {f : F} {I : TwoSidedIdeal R}
    {x : R} (hx : x ∈ I) : f x ∈ I.map f :=
  TwoSidedIdeal.subset_span ⟨x, hx, rfl⟩

lemma coe_map_of_surjective [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Surjective f)
    (I : TwoSidedIdeal R) : I.map f = f '' I := Set.ext_iff.2 fun x ↦
  ⟨I.mem_image_of_mem_map_of_surjective hf, fun ⟨x, hx1, hx2⟩ ↦ by
    simpa [hx2] using I.mem_map_of_mem (f := f) <| (mem_iff I x).2 hx1⟩

end NonUnitalNonAssoc

variable {R S F : Type*} [Ring R] [Ring S] [FunLike F R S]

@[simp]
lemma bot_toTwoSided : (⊥ : Ideal R).toTwoSided = ⊥ := by ext; simp

lemma comap_toTwoSided (f : F) (I : Ideal S) [RingHomClass F R S] [I.IsTwoSided] :
    (I.comap f).toTwoSided = (I.toTwoSided).comap f := by
  ext; simp [mem_comap]

lemma map_eq_bot_iff_le_ker {f : F} [RingHomClass F R S] (I : TwoSidedIdeal R) :
    I.map f = ⊥ ↔ I ≤ (RingHom.ker f).toTwoSided := by
  unfold RingHom.ker
  rw [comap_toTwoSided, bot_toTwoSided, ← map_le_iff_le_comap, le_bot_iff]

lemma mem_map_iff_of_surjective [RingHomClass F R S] {f : F} (hf : Function.Surjective f)
    {I : TwoSidedIdeal R} (hker : RingHom.ker f ≤ I.asIdeal) {x : R} :
    f x ∈ I.map f ↔ x ∈ I := by
  refine ⟨fun h ↦ ?_, fun h ↦ TwoSidedIdeal.mem_map_of_mem h⟩
  obtain ⟨z, hz, hzx⟩ := I.mem_image_of_mem_map_of_surjective hf h
  have hxz : x - z ∈ RingHom.ker f := by rw [RingHom.mem_ker, map_sub, hzx, sub_self]
  simpa using I.add_mem (mem_asIdeal.1 (hker hxz)) hz

lemma map_comap_of_surjective [RingHomClass F R S] {f : F} (hf : Function.Surjective f)
    (I : TwoSidedIdeal S) : (I.comap f).map f = I :=
  le_antisymm (map_le_iff_le_comap _ _|>.2 le_rfl) fun s hsi ↦
    let ⟨_, hfrs⟩ := hf s
    hfrs ▸ (TwoSidedIdeal.mem_map_of_mem <| mem_comap _|>.2 <| hfrs ▸ hsi)

lemma gc_map_comap (f : F) [NonUnitalRingHomClass F R S] :
    GaloisConnection (TwoSidedIdeal.map f) (TwoSidedIdeal.comap f) :=
  TwoSidedIdeal.map_le_iff_le_comap

variable {I J} in
lemma map_le_of_le_comap [RingHomClass F R S] {f : F} {I : TwoSidedIdeal R} {J : TwoSidedIdeal S} :
    I ≤ J.comap f → I.map f ≤ J := (gc_map_comap f).l_le

variable {I J} in
lemma le_comap_of_map_le [RingHomClass F R S] {f : F} {I : TwoSidedIdeal R} {J : TwoSidedIdeal S} :
    I.map f ≤ J → I ≤ J.comap f := (gc_map_comap f).le_u

lemma comap_le_comap_iff_of_surjective [RingHomClass F R S] {f : F} (hf : Function.Surjective f)
    {I J : TwoSidedIdeal S} :
    I.comap f ≤ J.comap f ↔ I ≤ J :=
    ⟨fun h => (map_comap_of_surjective hf I).symm.le.trans (map_le_of_le_comap h), fun h =>
    le_comap_of_map_le ((map_comap_of_surjective hf I).le.trans h)⟩

lemma _root_.Ideal.toTwoSided_le_iff {I : Ideal R} [I.IsTwoSided] {J : TwoSidedIdeal R} :
    I.toTwoSided ≤ J ↔ I ≤ J.asIdeal :=
  ⟨fun h _ hx ↦ mem_asIdeal.2 <| h <| Ideal.mem_toTwoSided.2 hx,
   fun h _ hx ↦ mem_asIdeal.1 <| h <| Ideal.mem_toTwoSided.1 hx⟩

lemma span_le_twoSided (s : Set R) :
    Ideal.span s ≤ (span s).asIdeal := fun x hx ↦ by
  simp only [Ideal.mem_span, mem_asIdeal, mem_span_iff] at hx ⊢
  exact fun I hI ↦ by simpa using hx I.asIdeal (by simpa using hI)

lemma map_le_twoSided {f : F} (I : TwoSidedIdeal R) :
    I.asIdeal.map f ≤ (I.map f).asIdeal := span_le_twoSided _

@[simp]
lemma asIdeal_comap {f : F} [RingHomClass F R S] (I : TwoSidedIdeal S) :
    (I.comap f).asIdeal = I.asIdeal.comap f := by
  ext
  simp [mem_comap]

end TwoSidedIdeal
