import Proofs.Defs

open Classical

namespace OddStepSharp

def Above {X : Type*} [LinearOrder X]
    (A : Finset (X → Bool)) (x : X) : Prop :=
  ∀ u ∈ A, ∀ v ∈ A, ∀ y, x < y → u y = v y

def Split {X : Type*} [LinearOrder X]
    (A : Finset (X → Bool)) (x : X) : Prop :=
  Above A x ∧ ∃ u ∈ A, ∃ v ∈ A, u x ≠ v x

def side {X : Type*}
    (A : Finset (X → Bool)) (x : X) (b : Bool) :
    Finset (X → Bool) :=
  A.filter (fun v => v x = b)

def Balanced {X : Type*} [LinearOrder X]
    (A : Finset (X → Bool)) : Prop :=
  ∃ x : X, Above A x ∧
    2 ≤ (side A x false).card ∧
    2 ≤ (side A x true).card

def Cat {X : Type*} [LinearOrder X]
    (A : Finset (X → Bool)) : Prop :=
  ∀ B : Finset (X → Bool), B ⊆ A → B.card = 4 → ¬ Balanced B

noncomputable def levels {X : Type*} [LinearOrder X] [Fintype X]
    (A : Finset (X → Bool)) : Finset X :=
  Finset.univ.filter
    (fun x => ∃ u ∈ A, ∃ v ∈ A,
      u x ≠ v x ∧ ∀ y, x < y → u y = v y)

def OddSplit {X : Type*} [LinearOrder X]
    (A : Finset (X → Bool)) : Prop :=
  ∃ x : X, Split A x ∧ 3 ≤ (side A x false).card ∧
    3 ≤ (side A x true).card ∧
    (side A x false).card % 2 = 1 ∧ (side A x true).card % 2 = 1

noncomputable def colour {X C : Type*} [LinearOrder X] [Fintype X]
    (a b : C) (χ : Finset X → C) (A : Finset (X → Bool)) : C :=
  if Cat A then χ (levels A)
  else if OddSplit A then a else b

end OddStepSharp

namespace OddSharpEx

lemma lt_two_pow' (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      omega

lemma card_pair_le {α : Type*} [DecidableEq α] (p q : α) :
    ({p, q} : Finset α).card ≤ 2 := by
  have h1 := Finset.card_insert_le p ({q} : Finset α)
  rw [Finset.card_singleton] at h1
  omega

lemma fin_lt {N : ℕ} (x y : Fin N) (h : x.val < y.val) : x < y :=
  Fin.lt_def.mpr h

lemma mem_side' {X : Type*} (A : Finset (X → Bool)) (x : X) (b : Bool) (v : X → Bool) :
    v ∈ OddStepSharp.side A x b ↔ v ∈ A ∧ v x = b :=
  Finset.mem_filter

/-- With the constant input colouring `b`, a set that is not odd-split gets colour `b`. -/
lemma colour_const {X C : Type*} [LinearOrder X] [Fintype X] (a b : C)
    (A : Finset (X → Bool)) (h : ¬ OddStepSharp.OddSplit A) :
    OddStepSharp.colour a b (fun _ : Finset X => b) A = b := by
  by_cases hc : OddStepSharp.Cat A
  · have e : OddStepSharp.colour a b (fun _ : Finset X => b) A =
        (fun _ : Finset X => b) (OddStepSharp.levels A) := by
      unfold OddStepSharp.colour
      rw [if_pos hc]
    exact e
  · unfold OddStepSharp.colour
    rw [if_neg hc, if_neg h]

/-- The point `v` with coordinate `c` set to `true`. -/
noncomputable def setb (N c : ℕ) (v : Fin N → Bool) (i : Fin N) : Bool :=
  if i.val = c then true else v i

/-- All points that are `false` at every coordinate from `c` on. -/
noncomputable def cube (N : ℕ) : ℕ → Finset (Fin N → Bool)
  | 0 => {fun _ => false}
  | c + 1 => cube N c ∪ (cube N c).image (setb N c)

/-- The spine point at level `lv`: `true` at `lv`, and also at `0` when `c` is `true`. -/
noncomputable def sp (N lv : ℕ) (c : Bool) (i : Fin N) : Bool :=
  if i.val = lv then true else if i.val = 0 then c else false

/-- Two spine points at each level `h + j < N`. -/
noncomputable def spine (N h : ℕ) : Finset (Fin N → Bool) :=
  (Finset.range (N - h)).image (fun j => sp N (h + j) false) ∪
    (Finset.range (N - h)).image (fun j => sp N (h + j) true)

lemma cube_zero (N : ℕ) : cube N 0 = {fun _ => false} := rfl

lemma cube_succ (N c : ℕ) :
    cube N (c + 1) = cube N c ∪ (cube N c).image (setb N c) := rfl

lemma cube_high (N : ℕ) :
    ∀ c : ℕ, ∀ v ∈ cube N c, ∀ i : Fin N, c ≤ i.val → v i = false := by
  intro c
  induction c with
  | zero =>
      intro v hv i _
      rw [cube_zero, Finset.mem_singleton] at hv
      subst hv
      rfl
  | succ c ih =>
      intro v hv i hi
      rw [cube_succ] at hv
      rcases Finset.mem_union.mp hv with h1 | h1
      · exact ih v h1 i (by omega)
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp h1
        have hne : ¬ (i.val = c) := by omega
        unfold setb
        rw [if_neg hne]
        exact ih w hw i (by omega)

lemma setb_inj (N c : ℕ) :
    Set.InjOn (setb N c) (cube N c : Set (Fin N → Bool)) := by
  intro v hv w hw hvw
  funext i
  by_cases hi : i.val = c
  · rw [cube_high N c v (Finset.mem_coe.mp hv) i (by omega),
      cube_high N c w (Finset.mem_coe.mp hw) i (by omega)]
  · have h := congrFun hvw i
    unfold setb at h
    rw [if_neg hi, if_neg hi] at h
    exact h

lemma cube_card (N : ℕ) : ∀ c : ℕ, c ≤ N → (cube N c).card = 2 ^ c := by
  intro c
  induction c with
  | zero =>
      intro _
      rw [cube_zero, Finset.card_singleton, pow_zero]
  | succ c ih =>
      intro hc
      obtain ⟨y, hy⟩ : ∃ y : Fin N, y.val = c := ⟨⟨c, by omega⟩, rfl⟩
      have hdisj : Disjoint (cube N c) ((cube N c).image (setb N c)) := by
        rw [Finset.disjoint_left]
        intro v hv hv2
        obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv2
        have h1 := cube_high N c (setb N c w) hv y (by omega)
        unfold setb at h1
        rw [if_pos hy] at h1
        exact absurd h1 (by decide)
      rw [cube_succ, Finset.card_union_of_disjoint hdisj,
        Finset.card_image_of_injOn (setb_inj N c), ih (by omega), pow_succ]
      omega

lemma img_at (N t : ℕ) (v : Fin N → Bool) (hv : v ∈ (cube N t).image (setb N t))
    (i : Fin N) : (i.val = t → v i = true) ∧ (t < i.val → v i = false) := by
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
  constructor
  · intro hi
    unfold setb
    rw [if_pos hi]
  · intro hi
    have hne : ¬ (i.val = t) := by omega
    unfold setb
    rw [if_neg hne]
    exact cube_high N t w hw i (by omega)

lemma sp_self (N lv : ℕ) (c : Bool) (i : Fin N) (hi : i.val = lv) :
    sp N lv c i = true := by
  unfold sp
  rw [if_pos hi]

lemma sp_off (N lv : ℕ) (c : Bool) (i : Fin N) (hi : ¬ (i.val = lv)) (h0 : ¬ (i.val = 0)) :
    sp N lv c i = false := by
  unfold sp
  rw [if_neg hi, if_neg h0]

lemma sp_zero (N lv : ℕ) (c : Bool) (i : Fin N) (hi : i.val = 0) (hlv : ¬ (lv = 0)) :
    sp N lv c i = c := by
  have hne : ¬ (i.val = lv) := by omega
  unfold sp
  rw [if_neg hne, if_pos hi]

lemma mem_spine (N h : ℕ) (v : Fin N → Bool) (hv : v ∈ spine N h) :
    ∃ lv : ℕ, ∃ c : Bool, h ≤ lv ∧ lv < N ∧ v = sp N lv c := by
  unfold spine at hv
  rcases Finset.mem_union.mp hv with h1 | h1
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h1
    have hj' := Finset.mem_range.mp hj
    exact ⟨h + j, false, by omega, by omega, rfl⟩
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h1
    have hj' := Finset.mem_range.mp hj
    exact ⟨h + j, true, by omega, by omega, rfl⟩

lemma sp_inj (N h : ℕ) (hh : 1 ≤ h) (c : Bool) :
    Set.InjOn (fun j => sp N (h + j) c) (Finset.range (N - h) : Set ℕ) := by
  intro j hj j' _ he
  have hj1 : j < N - h := Finset.mem_range.mp (Finset.mem_coe.mp hj)
  by_contra hne
  obtain ⟨y, hy⟩ : ∃ y : Fin N, y.val = h + j := ⟨⟨h + j, by omega⟩, rfl⟩
  have h1 : sp N (h + j) c y = sp N (h + j') c y := congrFun he y
  rw [sp_self N (h + j) c y hy, sp_off N (h + j') c y (by omega) (by omega)] at h1
  exact absurd h1 (by decide)

lemma spine_card (N h : ℕ) (hh : 1 ≤ h) (hN : h < N) :
    (spine N h).card = 2 * (N - h) := by
  obtain ⟨y, hy⟩ : ∃ y : Fin N, y.val = 0 := ⟨⟨0, by omega⟩, rfl⟩
  have hdisj : Disjoint ((Finset.range (N - h)).image (fun j => sp N (h + j) false))
      ((Finset.range (N - h)).image (fun j => sp N (h + j) true)) := by
    rw [Finset.disjoint_left]
    intro v hv hv2
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨j', _, he⟩ := Finset.mem_image.mp hv2
    have h1 : sp N (h + j') true y = sp N (h + j) false y := congrFun he y
    rw [sp_zero N (h + j') true y hy (by omega), sp_zero N (h + j) false y hy (by omega)] at h1
    exact absurd h1 (by decide)
  unfold spine
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn (sp_inj N h hh false),
    Finset.card_image_of_injOn (sp_inj N h hh true), Finset.card_range]
  omega

/-- A point of `C ∪ spine N h` that is `true` at a coordinate `i ≥ h` is one of the two spine points at
level `i`, when every point of `C` is `false` from coordinate `h` on. -/
lemma pair (N h : ℕ) (hh : 1 ≤ h) (C : Finset (Fin N → Bool))
    (hC : ∀ v ∈ C, ∀ i : Fin N, h ≤ i.val → v i = false)
    (v : Fin N → Bool) (hv : v ∈ C ∪ spine N h) (i : Fin N) (hi : h ≤ i.val)
    (hvi : v i = true) : v = sp N i.val false ∨ v = sp N i.val true := by
  rcases Finset.mem_union.mp hv with h1 | h1
  · rw [hC v h1 i hi] at hvi
    exact absurd hvi (by decide)
  · obtain ⟨lv, c, _, _, rfl⟩ := mem_spine N h v h1
    by_cases hl : i.val = lv
    · rw [hl]
      cases c
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rw [sp_off N lv c i hl (by omega)] at hvi
      exact absurd hvi (by decide)

/-- The construction, with `h = t + 1`: a core of `k + 1` points on the coordinates up to `t` (the
whole cube below `t`, with `2 ^ t` points, and `k + 1 - 2 ^ t` points that are `true` at `t`), and two
spine points at each level from `t + 1` to `N - 1`. No `(k + 1)`-subset is odd-split. -/
theorem construction (N t k : ℕ) (hk : 5 ≤ k) (htN : t + 2 ≤ N)
    (hlo : 2 ^ t < k + 1) (hhi : k + 1 ≤ 2 * 2 ^ t) (hev : 2 ^ t % 2 = 0) :
    ∃ K : Finset (Fin N → Bool), K.card = k + 1 + 2 * (N - (t + 1)) ∧
      ∀ A : Finset (Fin N → Bool), A ⊆ K → A.card = k + 1 →
        ¬ OddStepSharp.OddSplit A := by
  have hUc : (cube N t).card = 2 ^ t := cube_card N t (by omega)
  obtain ⟨T, hTV, hTc⟩ := Finset.exists_subset_card_eq
    (show k + 1 - 2 ^ t ≤ ((cube N t).image (setb N t)).card by
      rw [Finset.card_image_of_injOn (setb_inj N t), hUc]
      omega)
  have hU : ∀ v ∈ cube N t, ∀ i : Fin N, t ≤ i.val → v i = false := cube_high N t
  have hT1 : ∀ v ∈ T, ∀ i : Fin N, i.val = t → v i = true :=
    fun v hv i hi => (img_at N t v (hTV hv) i).1 hi
  have hT2 : ∀ v ∈ T, ∀ i : Fin N, t < i.val → v i = false :=
    fun v hv i hi => (img_at N t v (hTV hv) i).2 hi
  have hC : ∀ v ∈ cube N t ∪ T, ∀ i : Fin N, t + 1 ≤ i.val → v i = false := by
    intro v hv i hi
    rcases Finset.mem_union.mp hv with h1 | h1
    · exact hU v h1 i (by omega)
    · exact hT2 v h1 i (by omega)
  obtain ⟨yt, hyt⟩ : ∃ y : Fin N, y.val = t := ⟨⟨t, by omega⟩, rfl⟩
  have hdUT : Disjoint (cube N t) T := by
    rw [Finset.disjoint_left]
    intro v hv hv2
    have e1 := hU v hv yt (by omega)
    rw [hT1 v hv2 yt hyt] at e1
    exact absurd e1 (by decide)
  have hCc : (cube N t ∪ T).card = k + 1 := by
    rw [Finset.card_union_of_disjoint hdUT, hUc, hTc]
    omega
  have hdCS : Disjoint (cube N t ∪ T) (spine N (t + 1)) := by
    rw [Finset.disjoint_left]
    intro v hv hv2
    obtain ⟨lv, c, hl1, hl2, hvl⟩ := mem_spine N (t + 1) v hv2
    obtain ⟨y, hy⟩ : ∃ y : Fin N, y.val = lv := ⟨⟨lv, hl2⟩, rfl⟩
    have e1 := hC v hv y (by omega)
    rw [hvl, sp_self N lv c y hy] at e1
    exact absurd e1 (by decide)
  refine ⟨(cube N t ∪ T) ∪ spine N (t + 1), ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hdCS, hCc, spine_card N (t + 1) (by omega) (by omega)]
  · intro A hAK hAc hodd
    obtain ⟨x, hx, _, ht3, hfo, _⟩ := hodd
    by_cases hxh : t + 1 ≤ x.val
    · have hsub : OddStepSharp.side A x true ⊆ {sp N x.val false, sp N x.val true} := by
        intro v hv
        obtain ⟨hvA, hvx⟩ := (mem_side' A x true v).mp hv
        rcases pair N (t + 1) (by omega) (cube N t ∪ T) hC v (hAK hvA) x hxh hvx with e | e
        · rw [e]
          exact Finset.mem_insert_self _ _
        · rw [e]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      have h2 := Finset.card_le_card hsub
      have h3 := card_pair_le (sp N x.val false) (sp N x.val true)
      omega
    · have hAC : A ⊆ cube N t ∪ T := by
        intro v hv
        by_contra hvC
        have hvS : v ∈ spine N (t + 1) := by
          rcases Finset.mem_union.mp (hAK hv) with e | e
          · exact absurd e hvC
          · exact e
        obtain ⟨lv, c, hl1, hl2, hvl⟩ := mem_spine N (t + 1) v hvS
        obtain ⟨y, hy⟩ : ∃ y : Fin N, y.val = lv := ⟨⟨lv, hl2⟩, rfl⟩
        have hvy : v y = true := by
          rw [hvl]
          exact sp_self N lv c y hy
        have hsub : A ⊆ {sp N lv false, sp N lv true} := by
          intro u hu
          have huy : u y = true :=
            (hx.1 u hu v hv y (fin_lt x y (by omega))).trans hvy
          rcases pair N (t + 1) (by omega) (cube N t ∪ T) hC u (hAK hu) y (by omega) huy with e | e
          · rw [e, hy]
            exact Finset.mem_insert_self _ _
          · rw [e, hy]
            exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        have h2 := Finset.card_le_card hsub
        have h3 := card_pair_le (sp N lv false) (sp N lv true)
        omega
      have hAeq : A = cube N t ∪ T := Finset.eq_of_subset_of_card_le hAC (by omega)
      subst hAeq
      have hxt : x.val = t := by
        by_contra hne
        obtain ⟨p, hp⟩ := Finset.card_pos.mp (show 0 < (cube N t).card by omega)
        obtain ⟨q, hq⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
        have e := hx.1 p (Finset.mem_union_left T hp) q (Finset.mem_union_right (cube N t) hq)
          yt (fin_lt x yt (by omega))
        rw [hU p hp yt (by omega), hT1 q hq yt hyt] at e
        exact absurd e (by decide)
      have hside : OddStepSharp.side (cube N t ∪ T) x false = cube N t := by
        ext v
        rw [mem_side']
        constructor
        · rintro ⟨hvA, hvx⟩
          rcases Finset.mem_union.mp hvA with e | e
          · exact e
          · rw [hT1 v e x hxt] at hvx
            exact absurd hvx (by decide)
        · intro hv
          exact ⟨Finset.mem_union_left T hv, hU v hv x (by omega)⟩
      rw [hside, hUc] at hfo
      omega

lemma clog_le (k h : ℕ) (hh : h = Nat.clog 2 (k + 1)) : k + 1 ≤ 2 ^ h := by
  rw [hh]
  exact Nat.le_pow_clog (by norm_num) (k + 1)

lemma clog_lt (k t : ℕ) (hh : t + 1 = Nat.clog 2 (k + 1)) : 2 ^ t < k + 1 :=
  (Nat.lt_clog_iff_pow_lt (by norm_num)).mp (by omega)

end OddSharpEx

theorem odd_split_sharpness_example : ∀ {C : Type*} (k n : ℕ), 5 ≤ k → k % 2 = 1 → k + 1 ≤ n → ∀ (h : ℕ), h = Nat.clog 2 (k + 1) → ∀ (a b : C), a ≠ b → ∃ K : Finset (Fin (n - 1) → Bool), K.card = 2 * n + k - 2 * h - 1 ∧ ∀ A : Finset (Fin (n - 1) → Bool), A ⊆ K → A.card = k + 1 → OddStepSharp.colour a b (fun _ : Finset (Fin (n - 1)) => b) A = b := by
  intro C k n hk _ hn h hh a b _
  have F1 : k + 1 ≤ 2 ^ h := OddSharpEx.clog_le k h hh
  have h1 : 1 ≤ h := by
    by_contra h0
    have e0 : h = 0 := by omega
    rw [e0, pow_zero] at F1
    omega
  obtain ⟨t, rfl⟩ : ∃ t, h = t + 1 := ⟨h - 1, by omega⟩
  have hlo : 2 ^ t < k + 1 := OddSharpEx.clog_lt k t hh
  have hhi : k + 1 ≤ 2 * 2 ^ t := by
    rw [pow_succ] at F1
    omega
  have ht2 : 2 ≤ t := by
    by_contra hlt
    have h01 : t = 0 ∨ t = 1 := by omega
    rcases h01 with e0 | e1
    · rw [e0, pow_zero] at hhi
      omega
    · rw [e1, pow_one] at hhi
      omega
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 + 1 := ⟨t - 2, by omega⟩
  have hs := OddSharpEx.lt_two_pow' s
  have e2 : 2 ^ (s + 1 + 1) = 2 ^ s * 2 * 2 := by ring
  have htp : s + 1 + 1 + 2 ≤ 2 ^ (s + 1 + 1) := by
    rw [e2]
    omega
  have hev : 2 ^ (s + 1 + 1) % 2 = 0 := by
    rw [e2]
    omega
  obtain ⟨K, hKc, hKno⟩ :=
    OddSharpEx.construction (n - 1) (s + 1 + 1) k hk (by omega) hlo hhi hev
  refine ⟨K, by omega, ?_⟩
  intro A hAK hAc
  exact OddSharpEx.colour_const a b A (hKno A hAK hAc)

