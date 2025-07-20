import Mathlib.Data.DFinsupp.Submonoid
import Mathlib.Data.Finsupp.Basic

variable {ι γ β : Type*}

open Finsupp

@[to_additive]
theorem finsuppProd_mem [Zero β] [CommMonoid γ] {S : Type*} [SetLike S γ] [SubmonoidClass S γ]
    {s : S} {f : ι →₀ β} {g : ι → β → γ} (h : ∀ c, f c ≠ 0 → g c (f c) ∈ s) : f.prod g ∈ s :=
  prod_mem fun _ hi ↦ h _ <| mem_support_iff.1 hi
