/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import WeakConvergence.DistributionConvergence

/-!
# Existence in Theorem 12.7b: multivariate Stieltjes measures (SLP pp. 366–369)

Every `F : ℝˡ → ℝ` with `0 ≤ F ≤ 1` satisfying (D1)–(D3) is the distribution function of a unique
probability measure (`theorem_12_7b`). The book defines `λ` on finite unions of boxes and asserts
countable additivity by ordering the pieces of a countable decomposition of `(a, b]` as
`b = b₁ ≥ a₁ = b₂ ≥ …`, which is not possible in general when `l ≥ 2` (see `docs/corrections.md`).
The proof here is the standard one:

1. the vertex sum `Δ(a, b] = Σₜ (−1)^{l−|t|} F(a + θₜd)` is additive when a box is cut by a
   hyperplane (`vertexSum_split`), hence additive on every partition of a box into boxes
   (`boxContent`, through Mathlib's `BoxIntegral.BoxAdditiveMap.ofMapSplitAdd`);
2. half-open boxes together with `∅` form a semiring of sets (`isSetSemiring_boxes`), on which
   `Δ` is a finitely additive content (`stieltjesContent`);
3. the content is countably subadditive (`isSigmaSubadditive`): shrink the box to a compact set
   and enlarge the covering boxes to open ones using continuity from above (D2), then take a
   finite subcover;
4. Carathéodory's theorem (`AddContent.measure`) gives the measure, and the limits in (D1) give
   `λ((−∞, x]) = F(x)`.
-/

namespace StokeyLucasPrescott.WeakConvergence

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

variable {l : ℕ}

/-! ### The vertex sum is additive under cuts -/

/-- Grouping the vertex sum in pairs `u`, `insert i u`. -/
theorem vertexSum_eq_erase (F : (Fin l → ℝ) → ℝ) (a b : Fin l → ℝ) (i : Fin l) :
    vertexSum F a b = ∑ u ∈ (Finset.univ.erase i).powerset,
      (-1 : ℝ) ^ (l - (u.card + 1)) * (F (vertex a b (insert i u)) - F (vertex a b u)) := by
  have hu : (Finset.univ : Finset (Fin l)) = insert i (Finset.univ.erase i) :=
    (Finset.insert_erase (Finset.mem_univ i)).symm
  rw [vertexSum, ← Finset.powerset_univ]
  conv_lhs => rw [hu]
  rw [Finset.sum_powerset_insert (Finset.notMem_erase i _), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u hu' => ?_
  have hsub := Finset.mem_powerset.1 hu'
  have hiu : i ∉ u := fun h => Finset.notMem_erase i _ (hsub h)
  have hcard : u.card + 1 ≤ l := by
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin] at this
    have : 0 < l := Fin.pos i
    omega
  rw [Finset.card_insert_of_notMem hiu, show l - u.card = (l - (u.card + 1)) + 1 by omega,
    pow_succ]
  ring

/-- Cutting `(a, b]` by the hyperplane `xᵢ = x` splits the vertex sum. -/
theorem vertexSum_split (F : (Fin l → ℝ) → ℝ) (a b : Fin l → ℝ) (i : Fin l) (x : ℝ) :
    vertexSum F a (Function.update b i x) + vertexSum F (Function.update a i x) b =
      vertexSum F a b := by
  rw [vertexSum_eq_erase F a b i, vertexSum_eq_erase F a _ i, vertexSum_eq_erase F _ b i,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u hu' => ?_
  have hiu : i ∉ u := fun h => Finset.notMem_erase i _ (Finset.mem_powerset.1 hu' h)
  have e1 : vertex a (Function.update b i x) u = vertex a b u := funext fun j => by
    by_cases hj : j ∈ u
    · have hji : j ≠ i := fun h => hiu (h ▸ hj)
      simp [vertex, hj, Function.update_of_ne hji]
    · simp [vertex, hj]
  have e2 : vertex a (Function.update b i x) (insert i u) =
      vertex (Function.update a i x) b u := funext fun j => by
    by_cases hji : j = i
    · subst hji; simp [vertex, hiu]
    · by_cases hj : j ∈ u <;> simp [vertex, hj, hji]
  have e3 : vertex (Function.update a i x) b (insert i u) = vertex a b (insert i u) :=
    funext fun j => by
      by_cases hji : j = i
      · subst hji; simp [vertex]
      · by_cases hj : j ∈ u <;> simp [vertex, hj, hji]
  rw [e1, e2, e3]
  ring

/-- The vertex sum as a box-additive map: additive on every partition of a box into boxes. -/
noncomputable def boxContent (F : (Fin l → ℝ) → ℝ) : BoxIntegral.BoxAdditiveMap (Fin l) ℝ ⊤ :=
  BoxIntegral.BoxAdditiveMap.ofMapSplitAdd (fun I => vertexSum F I.lower I.upper) ⊤
    fun I _ i x hx => by
      rw [BoxIntegral.Box.splitLower_def hx, BoxIntegral.Box.splitUpper_def hx]
      exact vertexSum_split F I.lower I.upper i x

theorem boxContent_apply (F : (Fin l → ℝ) → ℝ) (I : BoxIntegral.Box (Fin l)) :
    boxContent F I = vertexSum F I.lower I.upper := rfl

/-! ### The semiring of boxes -/

/-- Half-open boxes `(a, b]`, together with `∅`. -/
def boxes : Set (Set (Fin l → ℝ)) := insert ∅ (range fun p : (Fin l → ℝ) × (Fin l → ℝ) =>
  box p.1 p.2)

theorem box_mem_boxes (a b : Fin l → ℝ) : box a b ∈ (boxes : Set (Set (Fin l → ℝ))) :=
  mem_insert_of_mem _ ⟨(a, b), rfl⟩

theorem coe_box_eq (I : BoxIntegral.Box (Fin l)) : (I : Set (Fin l → ℝ)) = box I.lower I.upper :=
  BoxIntegral.Box.coe_eq_pi I

/-- A member of `boxes` is empty or a `BoxIntegral` box. -/
theorem eq_empty_or_coe {s : Set (Fin l → ℝ)} (hs : s ∈ (boxes : Set (Set (Fin l → ℝ)))) :
    s = ∅ ∨ ∃ I : BoxIntegral.Box (Fin l), s = I := by
  rcases hs with rfl | ⟨⟨a, b⟩, rfl⟩
  · exact Or.inl rfl
  by_cases h : ∀ i, a i < b i
  · exact Or.inr ⟨⟨a, b, h⟩, (coe_box_eq (⟨a, b, h⟩ : BoxIntegral.Box (Fin l))).symm⟩
  · push Not at h
    obtain ⟨i, hi⟩ := h
    exact Or.inl (eq_empty_of_forall_notMem fun y hy => by
      have := hy i (mem_univ i); exact absurd (this.1.trans_le this.2) (not_lt.2 hi))

theorem coe_mem_boxes (I : BoxIntegral.Box (Fin l)) :
    (I : Set (Fin l → ℝ)) ∈ (boxes : Set (Set (Fin l → ℝ))) :=
  coe_box_eq I ▸ box_mem_boxes _ _

theorem isSetSemiring_boxes : IsSetSemiring (boxes : Set (Set (Fin l → ℝ))) where
  empty_mem := mem_insert _ _
  inter_mem s hs t ht := by
    rcases hs with rfl | ⟨⟨a, b⟩, rfl⟩
    · rw [empty_inter]; exact mem_insert _ _
    rcases ht with rfl | ⟨⟨c, d⟩, rfl⟩
    · rw [inter_empty]; exact mem_insert _ _
    simp only
    rw [box_inter]; exact box_mem_boxes _ _
  sdiff_eq_sUnion' s hs t ht := by
    classical
    rcases eq_empty_or_coe hs with rfl | ⟨I, rfl⟩
    · exact ⟨∅, by simp, by simp, by simp⟩
    have hst : (I : Set (Fin l → ℝ)) ∩ t ∈ (boxes : Set (Set (Fin l → ℝ))) := by
      rcases ht with rfl | ⟨⟨c, d⟩, rfl⟩
      · rw [inter_empty]; exact mem_insert _ _
      rw [coe_box_eq, box_inter]; exact box_mem_boxes _ _
    rw [← sdiff_inter_self_eq_sdiff, inter_comm]
    rcases eq_empty_or_coe hst with h | ⟨J, hJ⟩
    · rw [h, sdiff_empty]
      exact ⟨{(I : Set (Fin l → ℝ))}, by simpa using coe_mem_boxes I, by simp, by simp⟩
    have hJI : J ≤ I := (BoxIntegral.Box.coe_subset_coe).1 (hJ ▸ inter_subset_left)
    set π := (BoxIntegral.Prepartition.single I J hJI).compl
    refine ⟨π.boxes.image (↑), ?_, ?_, ?_⟩
    · intro u hu
      obtain ⟨K, -, rfl⟩ := Finset.mem_image.1 hu
      exact coe_mem_boxes K
    · intro u hu v hv huv
      obtain ⟨K₁, hK₁, rfl⟩ := Finset.mem_image.1 hu
      obtain ⟨K₂, hK₂, rfl⟩ := Finset.mem_image.1 hv
      exact π.disjoint_coe_of_mem hK₁ hK₂ fun h => huv (h ▸ rfl)
    · rw [hJ, ← BoxIntegral.Prepartition.iUnion_single hJI,
        ← BoxIntegral.Prepartition.iUnion_compl, BoxIntegral.Prepartition.iUnion_def',
        Finset.coe_image, sUnion_image, Finset.set_biUnion_coe]

/-! ### The content -/

variable {F : (Fin l → ℝ) → ℝ}

/-- A box as a set. -/
abbrev boxSet (J : BoxIntegral.Box (Fin l)) : Set (Fin l → ℝ) := J

open Classical in
/-- `Δ` on members of the semiring: `F`'s vertex sum on boxes, `0` on `∅`. -/
noncomputable def boxFun (F : (Fin l → ℝ) → ℝ) (s : Set (Fin l → ℝ)) : ℝ≥0∞ :=
  if h : ∃ I : BoxIntegral.Box (Fin l), (I : Set (Fin l → ℝ)) = s then
    ENNReal.ofReal (boxContent F h.choose) else 0

theorem boxFun_coe (I : BoxIntegral.Box (Fin l)) :
    boxFun F I = ENNReal.ofReal (boxContent F I) := by
  unfold boxFun
  split_ifs with h
  · rw [BoxIntegral.Box.injective_coe h.choose_spec]
  · exact absurd ⟨I, rfl⟩ h

theorem boxFun_of_notMem {s : Set (Fin l → ℝ)} (hs : s ∉ range ((↑) : BoxIntegral.Box (Fin l) →
    Set (Fin l → ℝ))) : boxFun F s = 0 := by
  unfold boxFun
  split_ifs with h
  · obtain ⟨I, hI⟩ := h; exact absurd ⟨I, hI⟩ hs
  · rfl

/-- The vertex sum as a finitely additive content on the semiring of boxes (needs (D3)). -/
noncomputable def stieltjesContent (F : (Fin l → ℝ) → ℝ)
    (hD3 : ∀ a b, a ≤ b → 0 ≤ vertexSum F a b) : AddContent ℝ≥0∞ (boxes : Set (Set (Fin l → ℝ)))
    where
  toFun := boxFun F
  empty' := boxFun_of_notMem fun ⟨I, hI⟩ => I.nonempty_coe.ne_empty hI
  sUnion' I hI hdis hU := by
    classical
    have hinj : InjOn (boxSet (l := l)) (boxSet ⁻¹' (I : Set (Set (Fin l → ℝ)))) :=
      BoxIntegral.Box.injective_coe.injOn
    rw [← Finset.sum_preimage boxSet I hinj (boxFun F) fun u _ hu => boxFun_of_notMem hu]
    have hmem : ∀ J, J ∈ I.preimage boxSet hinj → boxSet J ∈ I := fun J hJ =>
      Finset.mem_preimage.1 hJ
    rcases eq_empty_or_coe hU with h | ⟨I₀, hI₀⟩
    · have hsub : ∀ J ∈ I.preimage boxSet hinj, False := fun J hJ =>
        J.nonempty_coe.ne_empty (subset_empty_iff.1 (h ▸ subset_sUnion_of_mem
          (Finset.mem_coe.2 (hmem J hJ))))
      rw [h, Finset.sum_eq_zero fun J hJ => (hsub J hJ).elim]
      exact boxFun_of_notMem fun ⟨I, hI⟩ => I.nonempty_coe.ne_empty hI
    set π : BoxIntegral.Prepartition I₀ :=
      { boxes := I.preimage boxSet hinj
        le_of_mem' := fun J hJ => BoxIntegral.Box.coe_subset_coe.1
          (hI₀ ▸ subset_sUnion_of_mem (Finset.mem_coe.2 (hmem J hJ)))
        pairwiseDisjoint := fun J₁ hJ₁ J₂ hJ₂ hne =>
          hdis (Finset.mem_coe.2 (hmem J₁ hJ₁)) (Finset.mem_coe.2 (hmem J₂ hJ₂))
            fun h => hne (BoxIntegral.Box.injective_coe h) }
    have hπ : π.IsPartition := by
      rw [BoxIntegral.Prepartition.isPartition_iff_iUnion_eq,
        BoxIntegral.Prepartition.iUnion_def', ← hI₀]
      apply Subset.antisymm
      · exact iUnion₂_subset fun J hJ => subset_sUnion_of_mem (Finset.mem_coe.2 (hmem J hJ))
      · intro y hy
        obtain ⟨u, hu, hyu⟩ := mem_sUnion.1 hy
        rcases eq_empty_or_coe (hI hu) with rfl | ⟨J, rfl⟩
        · exact absurd hyu (notMem_empty y)
        · exact mem_iUnion₂.2 ⟨J, (Finset.mem_preimage (s := I) (f := boxSet) (hf := hinj)).2
            (Finset.mem_coe.1 hu), hyu⟩
    have hsum := (boxContent F).sum_partition_boxes le_top hπ
    rw [hI₀, boxFun_coe, ← hsum, ENNReal.ofReal_sum_of_nonneg (f := fun J => boxContent F J)
      fun J _ => hD3 _ _ fun i => (J.lower_lt_upper i).le]
    exact Finset.sum_congr rfl fun J _ => (boxFun_coe J).symm

theorem stieltjesContent_box (hD3 : ∀ a b, a ≤ b → 0 ≤ vertexSum F a b) {a b : Fin l → ℝ}
    (h : ∀ i, a i < b i) :
    stieltjesContent F hD3 (box a b) = ENNReal.ofReal (vertexSum F a b) := by
  have : box a b = ((⟨a, b, h⟩ : BoxIntegral.Box (Fin l)) : Set (Fin l → ℝ)) :=
    (coe_box_eq (⟨a, b, h⟩ : BoxIntegral.Box (Fin l))).symm
  change boxFun F (box a b) = _
  rw [this, boxFun_coe]; rfl

/-! ### Continuity from above in every nonnegative direction -/

/-- (D2) and monotonicity give `F(y + δe) → F(y)` as `δ ↓ 0` for every `0 ≤ e ≤ 1`. -/
theorem tendsto_shift (hmono : Monotone F) (hcont : ∀ x, ContFromAbove F x) (y : Fin l → ℝ)
    {e : Fin l → ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    Tendsto (fun δ : ℝ => F (y + δ • e)) (𝓝[>] 0) (𝓝 (F y)) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hcont y) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
    exact hmono fun i => by
      have := he0 i; simp only [Pi.zero_apply] at this
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; nlinarith
  · filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
    exact hmono fun i => by
      have := he1 i; simp only [Pi.one_apply] at this
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, diag]; nlinarith

/-- The indicator vector of a set of coordinates. -/
def indVec (t : Finset (Fin l)) : Fin l → ℝ := fun j => if j ∈ t then 1 else 0

theorem indVec_nonneg (t : Finset (Fin l)) : 0 ≤ indVec t := fun j => by
  simp only [indVec, Pi.zero_apply]; split_ifs <;> norm_num

theorem indVec_le_one (t : Finset (Fin l)) : indVec t ≤ 1 := fun j => by
  simp only [indVec, Pi.one_apply]; split_ifs <;> norm_num

theorem vertex_add_upper (a b : Fin l → ℝ) (t : Finset (Fin l)) (δ : ℝ) :
    vertex a (b + diag δ) t = vertex a b t + δ • indVec t := funext fun j => by
  by_cases hj : j ∈ t <;> simp [vertex, indVec, diag, hj]

theorem vertex_add_lower (a b : Fin l → ℝ) (t : Finset (Fin l)) (δ : ℝ) :
    vertex (a + diag δ) b t = vertex a b t + δ • indVec tᶜ := funext fun j => by
  by_cases hj : j ∈ t <;> simp [vertex, indVec, diag, hj]

theorem tendsto_vertexSum_upper (hmono : Monotone F) (hcont : ∀ x, ContFromAbove F x)
    (a b : Fin l → ℝ) :
    Tendsto (fun δ : ℝ => vertexSum F a (b + diag δ)) (𝓝[>] 0) (𝓝 (vertexSum F a b)) := by
  simp only [vertexSum, vertex_add_upper]
  exact tendsto_finsetSum _ fun t _ => (tendsto_shift hmono hcont _ (indVec_nonneg t)
    (indVec_le_one t)).const_mul _

theorem tendsto_vertexSum_lower (hmono : Monotone F) (hcont : ∀ x, ContFromAbove F x)
    (a b : Fin l → ℝ) :
    Tendsto (fun δ : ℝ => vertexSum F (a + diag δ) b) (𝓝[>] 0) (𝓝 (vertexSum F a b)) := by
  simp only [vertexSum, vertex_add_lower]
  exact tendsto_finsetSum _ fun t _ => (tendsto_shift hmono hcont _ (indVec_nonneg tᶜ)
    (indVec_le_one tᶜ)).const_mul _

/-! ### Countable subadditivity -/

theorem ofReal_le_ofReal_add {x y : ℝ} (ε : ℝ≥0) (hy : 0 ≤ y) (h : x ≤ y + ε) :
    ENNReal.ofReal x ≤ ENNReal.ofReal y + ε := by
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_add hy ε.coe_nonneg]
  exact ENNReal.ofReal_le_ofReal h

/-- Each member of the semiring lies in an open set inside a slightly larger box. -/
theorem exists_open_cover (hmono : Monotone F) (hcont : ∀ x, ContFromAbove F x)
    (hD3 : ∀ a b, a ≤ b → 0 ≤ vertexSum F a b) {s : Set (Fin l → ℝ)}
    (hs : s ∈ (boxes : Set (Set (Fin l → ℝ)))) {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ U V : Set (Fin l → ℝ), IsOpen U ∧ s ⊆ U ∧ U ⊆ V ∧ V ∈ (boxes : Set (Set (Fin l → ℝ))) ∧
      stieltjesContent F hD3 V ≤ stieltjesContent F hD3 s + ε := by
  rcases eq_empty_or_coe hs with rfl | ⟨I, rfl⟩
  · exact ⟨∅, ∅, isOpen_empty, subset_rfl, subset_rfl, mem_insert _ _, le_add_right le_rfl⟩
  have hlim := tendsto_vertexSum_upper hmono hcont I.lower I.upper
  obtain ⟨δ, hδlt, hδ0⟩ := ((hlim.eventually (gt_mem_nhds (show vertexSum F I.lower I.upper <
    vertexSum F I.lower I.upper + ε from lt_add_of_pos_right _ (NNReal.coe_pos.2 hε)))).and
    self_mem_nhdsWithin).exists
  have hδ0 : (0 : ℝ) < δ := hδ0
  have hlt : ∀ i, I.lower i < (I.upper + diag δ : Fin l → ℝ) i := fun i => by
    simp only [Pi.add_apply, diag]; linarith [I.lower_lt_upper i]
  refine ⟨Set.pi univ fun i => Ioo (I.lower i) (I.upper i + δ), box I.lower (I.upper + diag δ),
    isOpen_set_pi finite_univ fun i _ => isOpen_Ioo, ?_, ?_, box_mem_boxes _ _, ?_⟩
  · rw [coe_box_eq]
    exact fun y hy i _ => ⟨(hy i (mem_univ i)).1, by linarith [(hy i (mem_univ i)).2]⟩
  · exact fun y hy i _ => ⟨(hy i (mem_univ i)).1, by
      simp only [Pi.add_apply, diag]; exact (hy i (mem_univ i)).2.le⟩
  · rw [stieltjesContent_box hD3 hlt]
    change _ ≤ boxFun F I + ε
    rw [boxFun_coe]
    exact ofReal_le_ofReal_add ε (hD3 _ _ fun i => (I.lower_lt_upper i).le) hδlt.le

/-- Each box contains a compact set containing a slightly smaller box. -/
theorem exists_compact_inner (hmono : Monotone F) (hcont : ∀ x, ContFromAbove F x)
    (hD3 : ∀ a b, a ≤ b → 0 ≤ vertexSum F a b) (I : BoxIntegral.Box (Fin l)) {ε : ℝ≥0}
    (hε : 0 < ε) :
    ∃ K W : Set (Fin l → ℝ), IsCompact K ∧ W ⊆ K ∧ K ⊆ I ∧
      W ∈ (boxes : Set (Set (Fin l → ℝ))) ∧
      stieltjesContent F hD3 I ≤ stieltjesContent F hD3 W + ε := by
  have hlim := tendsto_vertexSum_lower hmono hcont I.lower I.upper
  have hgap : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ i, δ < I.upper i - I.lower i :=
    eventually_all.2 fun i => nhdsWithin_le_nhds (gt_mem_nhds (sub_pos.2 (I.lower_lt_upper i)))
  obtain ⟨δ, ⟨hδlt, hδgap⟩, hδ0⟩ := (((hlim.eventually (lt_mem_nhds (show
    vertexSum F I.lower I.upper - ε < vertexSum F I.lower I.upper by
      exact sub_lt_self _ (NNReal.coe_pos.2 hε)))).and hgap).and self_mem_nhdsWithin).exists
  have hδ0 : (0 : ℝ) < δ := hδ0
  have hlt : ∀ i, (I.lower + diag δ : Fin l → ℝ) i < I.upper i := fun i => by
    simp only [Pi.add_apply, diag]; linarith [hδgap i]
  refine ⟨Icc (I.lower + diag δ) I.upper, box (I.lower + diag δ) I.upper, isCompact_Icc,
    fun y hy => ⟨fun i => (hy i (mem_univ i)).1.le, fun i => (hy i (mem_univ i)).2⟩, ?_,
    box_mem_boxes _ _, ?_⟩
  · rw [coe_box_eq]
    intro y hy i _
    have h1 := hy.1 i; have h2 := hy.2 i
    simp only [Pi.add_apply, diag] at h1
    exact ⟨by linarith, h2⟩
  · rw [stieltjesContent_box hD3 hlt]
    change boxFun F I ≤ _
    rw [boxFun_coe]
    exact ofReal_le_ofReal_add ε (hD3 _ _ fun i => (hlt i).le) (by
      rw [boxContent_apply]; linarith)

/-- The content is countably subadditive. -/
theorem isSigmaSubadditive (hmono : Monotone F) (hcont : ∀ x, ContFromAbove F x)
    (hD3 : ∀ a b, a ≤ b → 0 ≤ vertexSum F a b) :
    (stieltjesContent F hD3).IsSigmaSubadditive := by
  intro f hf hU
  set m := stieltjesContent F hD3
  rcases eq_empty_or_coe hU with h | ⟨I, hI⟩
  · rw [h, addContent_empty]; exact zero_le
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨ε', hε'0, hε'sum⟩ := ENNReal.exists_pos_sum_of_countable
    (ENNReal.coe_ne_zero.2 hε2.ne') ℕ
  choose U V hUo hfU hUV hV hmV using fun n => exists_open_cover hmono hcont hD3 (hf n)
    (hε'0 n)
  obtain ⟨K, W, hK, hWK, hKI, hW, hmW⟩ := exists_compact_inner hmono hcont hD3 I hε2
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hUo
    (hKI.trans (hI ▸ iUnion_mono hfU))
  classical
  have hWsub : W ⊆ ⋃₀ ↑(t.image V) := by
    intro y hy
    obtain ⟨n, hn, hyn⟩ := mem_iUnion₂.1 (ht (hWK hy))
    exact mem_sUnion.2 ⟨V n, Finset.mem_coe.2 (Finset.mem_image_of_mem V hn), hUV n hyn⟩
  have h1 : m W ≤ ∑ u ∈ t.image V, m u :=
    addContent_le_sum_of_subset_sUnion isSetSemiring_boxes
      (fun u hu => by
        obtain ⟨n, -, rfl⟩ := Finset.mem_image.1 hu
        exact hV n) hW hWsub
  have h2 : ∑ u ∈ t.image V, m u ≤ ∑ n ∈ t, m (V n) := Finset.sum_image_le_of_nonneg
    fun _ _ => zero_le
  have h3 : ∑ n ∈ t, m (V n) ≤ ∑' n, m (f n) + ((ε / 2 : ℝ≥0) : ℝ≥0∞) := by
    calc ∑ n ∈ t, m (V n) ≤ ∑ n ∈ t, (m (f n) + ε' n) := Finset.sum_le_sum fun n _ => hmV n
      _ = ∑ n ∈ t, m (f n) + ∑ n ∈ t, (ε' n : ℝ≥0∞) := Finset.sum_add_distrib
      _ ≤ ∑' n, m (f n) + ∑' n, (ε' n : ℝ≥0∞) :=
          add_le_add (ENNReal.sum_le_tsum t) (ENNReal.sum_le_tsum t)
      _ ≤ ∑' n, m (f n) + ((ε / 2 : ℝ≥0) : ℝ≥0∞) := add_le_add le_rfl hε'sum.le
  rw [hI]
  calc m I ≤ m W + (ε / 2 : ℝ≥0) := hmW
    _ ≤ ∑' n, m (f n) + (ε / 2 : ℝ≥0) + (ε / 2 : ℝ≥0) := by
        gcongr; exact h1.trans (h2.trans h3)
    _ = ∑' n, m (f n) + ε := by
        rw [add_assoc, ← ENNReal.coe_add, add_halves]

/-! ### Generation and the measure -/

theorem Iic_eq_iUnion_box (x : Fin l → ℝ) :
    Iic x = ⋃ n : ℕ, box (x - diag ((n : ℝ) + 1)) x := by
  ext y
  simp only [mem_Iic, mem_iUnion, box, Set.mem_pi, mem_univ, true_implies, mem_Ioc,
    Pi.sub_apply, diag]
  constructor
  · intro hy
    obtain ⟨n, hn⟩ := exists_nat_gt (∑ i, (x i - y i))
    refine ⟨n, fun i => ⟨?_, hy i⟩⟩
    have : x i - y i ≤ ∑ j, (x j - y j) :=
      Finset.single_le_sum (f := fun j => x j - y j) (fun j _ => sub_nonneg.2 (hy j))
        (Finset.mem_univ i)
    linarith
  · rintro ⟨n, hn⟩ i
    exact (hn i).2

theorem borel_eq_generateFrom_boxes :
    (MeasurableSpace.pi : MeasurableSpace (Fin l → ℝ)) =
      MeasurableSpace.generateFrom (boxes : Set (Set (Fin l → ℝ))) := by
  apply le_antisymm
  · rw [← generateFrom_Iic_pi]
    refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨x, rfl⟩
    beta_reduce
    rw [Iic_eq_iUnion_box]
    exact MeasurableSet.iUnion fun n =>
      MeasurableSpace.measurableSet_generateFrom (box_mem_boxes _ _)
  · refine MeasurableSpace.generateFrom_le ?_
    rintro _ (rfl | ⟨⟨a, b⟩, rfl⟩)
    · exact MeasurableSet.empty
    · exact measurableSet_box a b

/-- `Δ((x - n1, x]) → F(x)` as `n → ∞`, by the limits of (D1). -/
theorem tendsto_vertexSum_Iic (h0 : ∀ x, 0 ≤ F x)
    (hlow : ∀ i, ∀ ε > 0, ∃ M, ∀ x : Fin l → ℝ, x i ≤ M → F x < ε) (x : Fin l → ℝ) :
    Tendsto (fun n : ℕ => vertexSum F (x - diag ((n : ℝ) + 1)) x) atTop (𝓝 (F x)) := by
  have hterm : ∀ t : Finset (Fin l), Tendsto (fun n : ℕ => F (vertex (x - diag ((n : ℝ) + 1)) x t))
      atTop (𝓝 (if t = Finset.univ then F x else 0)) := fun t => by
    split_ifs with ht
    · subst ht
      have : ∀ n : ℕ, vertex (x - diag ((n : ℝ) + 1)) x Finset.univ = x := fun n =>
        funext fun j => by simp [vertex]
      simp only [this]; exact tendsto_const_nhds
    · obtain ⟨i, hi⟩ : ∃ i, i ∉ t := by
        by_contra hne; push Not at hne; exact ht (Finset.eq_univ_iff_forall.2 hne)
      rw [tendsto_order]
      refine ⟨fun c hc => Eventually.of_forall fun n => lt_of_lt_of_le hc (h0 _),
        fun c hc => ?_⟩
      obtain ⟨M, hM⟩ := hlow i c hc
      obtain ⟨N, hN⟩ := exists_nat_gt (x i - M)
      refine eventually_atTop.2 ⟨N, fun n hn => hM _ ?_⟩
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      simp only [vertex, hi, ↓reduceIte, Pi.sub_apply, diag]
      linarith
  have := tendsto_finsetSum Finset.univ fun t _ => (hterm t).const_mul ((-1 : ℝ) ^ (l - t.card))
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    Finset.card_univ, Fintype.card_fin, Nat.sub_self, pow_zero, one_mul] at this
  exact this

/-- **Theorem 12.7b** (existence and uniqueness). If `F : ℝˡ → [0, 1]` satisfies (D1) (it is
nondecreasing, tends to `0` as any coordinate tends to `−∞` and to `1` as all coordinates tend to
`+∞`), (D2) (it is continuous from above) and (D3) (its vertex sums are nonnegative), then `F` is
the distribution function of exactly one probability measure. -/
theorem theorem_12_7b (F : (Fin l → ℝ) → ℝ) (h0 : ∀ x, 0 ≤ F x) (h1 : ∀ x, F x ≤ 1)
    (hmono : Monotone F) (hlow : ∀ i, ∀ ε > 0, ∃ M, ∀ x : Fin l → ℝ, x i ≤ M → F x < ε)
    (hup : ∀ ε > 0, ∃ M, ∀ x : Fin l → ℝ, (∀ i, M ≤ x i) → 1 - ε < F x)
    (hcont : ∀ x, ContFromAbove F x) (hD3 : ∀ a b, a ≤ b → 0 ≤ vertexSum F a b) :
    ∃! μ : Measure (Fin l → ℝ), IsProbabilityMeasure μ ∧ distFun μ = F := by
  set m := stieltjesContent F hD3
  set μ : Measure (Fin l → ℝ) := m.measure isSetSemiring_boxes borel_eq_generateFrom_boxes.le
    (isSigmaSubadditive hmono hcont hD3)
  have hμbox : ∀ a b : Fin l → ℝ, μ (box a b) = m (box a b) := fun a b =>
    m.measure_eq isSetSemiring_boxes borel_eq_generateFrom_boxes _ (box_mem_boxes a b)
  have hIic : ∀ x, μ (Iic x) = ENNReal.ofReal (F x) := fun x => by
    have hmono' : Monotone fun n : ℕ => box (x - diag ((n : ℝ) + 1)) x := fun m n hmn y hy i _ =>
      ⟨by
        have := (hy i (mem_univ i)).1
        simp only [Pi.sub_apply, diag] at this ⊢
        have : (m : ℝ) ≤ n := by exact_mod_cast hmn
        linarith, (hy i (mem_univ i)).2⟩
    have hA := tendsto_measure_iUnion_atTop (μ := μ) hmono'
    rw [← Iic_eq_iUnion_box] at hA
    have hB : Tendsto (fun n : ℕ => μ (box (x - diag ((n : ℝ) + 1)) x)) atTop
        (𝓝 (ENNReal.ofReal (F x))) := by
      have : ∀ n : ℕ, μ (box (x - diag ((n : ℝ) + 1)) x) =
          ENNReal.ofReal (vertexSum F (x - diag ((n : ℝ) + 1)) x) := fun n => by
        rw [hμbox, stieltjesContent_box hD3 fun i => by
          simp only [Pi.sub_apply, diag]; linarith [n.cast_nonneg (α := ℝ)]]
      simp only [this]
      exact (ENNReal.continuous_ofReal.tendsto _).comp (tendsto_vertexSum_Iic h0 hlow x)
    exact tendsto_nhds_unique hA hB
  have hprob : IsProbabilityMeasure μ := by
    constructor
    have hmono' : Monotone fun n : ℕ => Iic (diag (n : ℝ) : Fin l → ℝ) := fun m n hmn =>
      Iic_subset_Iic.2 fun i => by simp only [diag]; exact_mod_cast hmn
    have hU : (⋃ n : ℕ, Iic (diag (n : ℝ) : Fin l → ℝ)) = univ := eq_univ_of_forall fun y => by
      obtain ⟨n, hn⟩ := exists_nat_gt (∑ i, |y i|)
      refine mem_iUnion.2 ⟨n, fun i => ?_⟩
      have : |y i| ≤ ∑ j, |y j| := Finset.single_le_sum (f := fun j => |y j|)
        (fun j _ => abs_nonneg _) (Finset.mem_univ i)
      simp only [diag]; linarith [le_abs_self (y i)]
    have hA := tendsto_measure_iUnion_atTop (μ := μ) hmono'
    rw [hU] at hA
    have hF1 : Tendsto (fun n : ℕ => F (diag (n : ℝ))) atTop (𝓝 1) := by
      rw [tendsto_order]
      refine ⟨fun c hc => ?_, fun c hc => Eventually.of_forall fun n => (h1 _).trans_lt hc⟩
      obtain ⟨M, hM⟩ := hup (1 - c) (by linarith)
      obtain ⟨N, hN⟩ := exists_nat_gt M
      refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
      have := hM (diag (n : ℝ)) fun i => by
        simp only [diag]; linarith [show (N : ℝ) ≤ n by exact_mod_cast hn]
      linarith
    have hB : Tendsto (fun n : ℕ => μ (Iic (diag (n : ℝ) : Fin l → ℝ))) atTop (𝓝 1) := by
      simp only [hIic]
      rw [← ENNReal.ofReal_one]
      exact (ENNReal.continuous_ofReal.tendsto _).comp hF1
    exact tendsto_nhds_unique hA hB
  have hdist : distFun μ = F := funext fun x => by
    rw [distFun, measureReal_def, hIic, ENNReal.toReal_ofReal (h0 x)]
  exact ⟨μ, ⟨hprob, hdist⟩, fun ν ⟨_, hν⟩ => distFun_injective (hν.trans hdist.symm)⟩

end StokeyLucasPrescott.WeakConvergence
