import Proofs.Defs

set_option maxHeartbeats 0
set_option maxRecDepth 4096

open Classical

namespace WinStep

lemma ft : (false : Bool) ≠ true := by decide

lemma bool_cases (b : Bool) : b = false ∨ b = true := by
  cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma bool_eq : ∀ a b c : Bool, a ≠ b → c ≠ b → a = c := by
  intro a b c
  cases a <;> cases b <;> cases c <;> decide

lemma bool_ne : ∀ a b : Bool, a ≠ b →
    (a = false ∧ b = true) ∨ (a = true ∧ b = false) := by
  intro a b
  cases a <;> cases b <;> decide

lemma bool_ne_false : ∀ c : Bool, c ≠ false → c = true := by
  intro c
  cases c <;> decide

lemma bool_ne_true : ∀ c : Bool, c ≠ true → c = false := by
  intro c
  cases c <;> decide

lemma extend {V : Type*} [DecidableEq V]
    (S K : Finset V) (n : ℕ)
    (hSK : S ⊆ K) (hSn : S.card ≤ n) (hnK : n ≤ K.card) :
    ∃ A, S ⊆ A ∧ A ⊆ K ∧ A.card = n := by
  have he := Finset.card_sdiff_add_card_eq_card hSK
  obtain ⟨R, hR, hRc⟩ :=
    Finset.exists_subset_card_eq
      (show n - S.card ≤ (K \ S).card by omega)
  have hd : Disjoint S R := by
    rw [Finset.disjoint_left]
    intro v hv hw
    exact (Finset.mem_sdiff.mp (hR hw)).2 hv
  refine ⟨S ∪ R, fun v hv => Finset.mem_union_left _ hv,
    Finset.union_subset hSK
      (fun v hv => (Finset.mem_sdiff.mp (hR hv)).1), ?_⟩
  rw [Finset.card_union_of_disjoint hd]
  omega

lemma two_points {V : Type*} [DecidableEq V]
    (K : Finset V) (hK : 2 ≤ K.card) :
    ∃ u ∈ K, ∃ v ∈ K, u ≠ v := by
  obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq hK
  obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hTc
  exact ⟨u, hT (Finset.mem_insert_self _ _), v,
    hT (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)), huv⟩

lemma card_erase_ge {V : Type*} [DecidableEq V] (P : Finset V) (w : V) :
    P.card ≤ (P.erase w).card + 1 := by
  have hsub : P ⊆ insert w (P.erase w) := by
    intro v hv
    by_cases hvw : v = w
    · rw [hvw]
      exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hvw, hv⟩)
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_insert_le w (P.erase w)
  omega

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

lemma mem_side {X : Type*}
    (A : Finset (X → Bool)) (x : X) (b : Bool) (v : X → Bool) :
    v ∈ side A x b ↔ v ∈ A ∧ v x = b :=
  Finset.mem_filter

lemma side_subset {X : Type*}
    (A : Finset (X → Bool)) (x : X) (b : Bool) :
    side A x b ⊆ A :=
  Finset.filter_subset _ _

lemma above_sub {X : Type*} [LinearOrder X]
    {A B : Finset (X → Bool)} {x : X}
    (hAB : A ⊆ B) (hB : Above B x) : Above A x := by
  intro u hu v hv y hy
  exact hB u (hAB hu) v (hAB hv) y hy

lemma side_card_sum {X : Type*}
    (A : Finset (X → Bool)) (x : X) :
    (side A x false).card + (side A x true).card = A.card := by
  have hd : Disjoint (side A x false) (side A x true) := by
    rw [Finset.disjoint_left]
    intro v hv hw
    exact ft (((mem_side A x false v).mp hv).2.symm.trans
      ((mem_side A x true v).mp hw).2)
  have hu : side A x false ∪ side A x true = A := by
    ext v
    simp only [Finset.mem_union, mem_side]
    constructor
    · rintro (⟨hv, _⟩ | ⟨hv, _⟩) <;> exact hv
    · intro hv
      rcases bool_cases (v x) with h | h
      · exact Or.inl ⟨hv, h⟩
      · exact Or.inr ⟨hv, h⟩
  rw [← Finset.card_union_of_disjoint hd, hu]

lemma bits_disjoint {X : Type*}
    (x : X) (P Q : Finset (X → Bool))
    (hP : ∀ v ∈ P, v x = false)
    (hQ : ∀ v ∈ Q, v x = true) :
    Disjoint P Q := by
  rw [Finset.disjoint_left]
  intro v hv hw
  exact ft ((hP v hv).symm.trans (hQ v hw))

lemma sides_union {X : Type*} [Fintype X]
    (x : X) (P Q : Finset (X → Bool))
    (hP : ∀ v ∈ P, v x = false)
    (hQ : ∀ v ∈ Q, v x = true) :
    side (P ∪ Q) x false = P ∧ side (P ∪ Q) x true = Q := by
  constructor
  · ext v
    constructor
    · intro hv
      obtain ⟨hv, hb⟩ := (mem_side (P ∪ Q) x false v).mp hv
      rcases Finset.mem_union.mp hv with hp | hq
      · exact hp
      · exact (ft (hb.symm.trans (hQ v hq))).elim
    · intro hv
      exact (mem_side (P ∪ Q) x false v).mpr
        ⟨Finset.mem_union_left _ hv, hP v hv⟩
  · ext v
    constructor
    · intro hv
      obtain ⟨hv, hb⟩ := (mem_side (P ∪ Q) x true v).mp hv
      rcases Finset.mem_union.mp hv with hp | hq
      · exact (ft ((hP v hp).symm.trans hb)).elim
      · exact hq
    · intro hv
      exact (mem_side (P ∪ Q) x true v).mpr
        ⟨Finset.mem_union_right _ hv, hQ v hv⟩

lemma choose_side {X : Type*}
    (A : Finset (X → Bool)) (x : X) (b : Bool)
    (n : ℕ) (hn : n ≤ (side A x b).card) :
    ∃ P : Finset (X → Bool),
      P ⊆ A ∧ P.card = n ∧ ∀ v ∈ P, v x = b := by
  obtain ⟨P, hP, hPc⟩ := Finset.exists_subset_card_eq hn
  exact ⟨P, hP.trans (side_subset A x b), hPc,
    fun v hv => ((mem_side A x b v).mp (hP hv)).2⟩

lemma split_of_pos {X : Type*} [LinearOrder X]
    {A : Finset (X → Bool)} {x : X}
    (hA : Above A x)
    (hf : 0 < (side A x false).card)
    (ht : 0 < (side A x true).card) : Split A x := by
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hf
  obtain ⟨v, hv⟩ := Finset.card_pos.mp ht
  obtain ⟨huA, huf⟩ := (mem_side A x false u).mp hu
  obtain ⟨hvA, hvt⟩ := (mem_side A x true v).mp hv
  exact ⟨hA, u, huA, v, hvA,
    fun e => ft (huf.symm.trans (e.trans hvt))⟩

lemma split_pos {X : Type*} [LinearOrder X]
    {A : Finset (X → Bool)} {x : X}
    (h : Split A x) :
    0 < (side A x false).card ∧ 0 < (side A x true).card := by
  obtain ⟨_, u, hu, v, hv, huv⟩ := h
  rcases bool_ne (u x) (v x) huv with ⟨hf, ht⟩ | ⟨ht, hf⟩
  · exact ⟨Finset.card_pos.mpr
      ⟨u, (mem_side A x false u).mpr ⟨hu, hf⟩⟩,
      Finset.card_pos.mpr
      ⟨v, (mem_side A x true v).mpr ⟨hv, ht⟩⟩⟩
  · exact ⟨Finset.card_pos.mpr
      ⟨v, (mem_side A x false v).mpr ⟨hv, hf⟩⟩,
      Finset.card_pos.mpr
      ⟨u, (mem_side A x true u).mpr ⟨hu, ht⟩⟩⟩

lemma split_unique {X : Type*} [LinearOrder X]
    {A : Finset (X → Bool)} {x y : X}
    (hx : Split A x) (hy : Split A y) : x = y := by
  rcases lt_trichotomy x y with h | h | h
  · obtain ⟨u, hu, v, hv, hne⟩ := hy.2
    exact (hne (hx.1 u hu v hv y h)).elim
  · exact h
  · obtain ⟨u, hu, v, hv, hne⟩ := hx.2
    exact (hne (hy.1 u hu v hv x h)).elim

lemma top {X : Type*} [LinearOrder X] [Fintype X]
    (K : Finset (X → Bool)) (hK : 2 ≤ K.card) :
    ∃ x : X, Split K x := by
  obtain ⟨u, hu, v, hv, huv⟩ := two_points K hK
  let S : Finset X :=
    Finset.univ.filter
      (fun x => ∃ a ∈ K, ∃ b ∈ K, a x ≠ b x)
  have hmem : ∀ x, x ∈ S ↔ ∃ a ∈ K, ∃ b ∈ K, a x ≠ b x := by
    intro x
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
  have hS : S.Nonempty := by
    by_contra hn
    apply huv
    funext x
    by_contra hx
    exact hn ⟨x, (hmem x).mpr ⟨u, hu, v, hv, hx⟩⟩
  obtain ⟨x, hx, hmax⟩ :=
    Finset.exists_max_image S (fun x : X => x) hS
  refine ⟨x, ?_, (hmem x).mp hx⟩
  intro a ha b hb y hxy
  by_contra he
  have hy := (hmem y).mpr ⟨a, ha, b, hb, he⟩
  exact (not_le.mpr hxy) (hmax y hy)

lemma cat_sub {X : Type*} [LinearOrder X]
    {A B : Finset (X → Bool)} (hAB : A ⊆ B) (hB : Cat B) :
    Cat A := by
  intro D hD hc
  exact hB D (hD.trans hAB) hc

lemma cat_small {X : Type*} [LinearOrder X]
    (A : Finset (X → Bool)) (hA : A.card ≤ 3) : Cat A := by
  intro B hB hc
  have := Finset.card_le_card hB
  omega

lemma cat_split {X : Type*} [LinearOrder X] [Fintype X]
    {A : Finset (X → Bool)} {x : X}
    (hcat : Cat A) (hag : Above A x) :
    (side A x false).card ≤ 1 ∨ (side A x true).card ≤ 1 := by
  by_contra hn
  have hf : 2 ≤ (side A x false).card := by omega
  have ht : 2 ≤ (side A x true).card := by omega
  obtain ⟨P, hPA, hPc, hP⟩ := choose_side A x false 2 hf
  obtain ⟨Q, hQA, hQc, hQ⟩ := choose_side A x true 2 ht
  have hd := bits_disjoint x P Q hP hQ
  have he := sides_union x P Q hP hQ
  have hsub : P ∪ Q ⊆ A := Finset.union_subset hPA hQA
  have hc : (P ∪ Q).card = 4 := by
    rw [Finset.card_union_of_disjoint hd, hPc, hQc]
  apply hcat (P ∪ Q) hsub hc
  refine ⟨x, above_sub hsub hag, ?_, ?_⟩
  · rw [he.1, hPc]
  · rw [he.2, hQc]

lemma bad_four {X : Type*} [LinearOrder X]
    (A : Finset (X → Bool)) (hA : ¬ Cat A) :
    ∃ D : Finset (X → Bool),
      D ⊆ A ∧ D.card = 4 ∧ Balanced D := by
  by_contra hn
  apply hA
  intro D hD hc hb
  exact hn ⟨D, hD, hc, hb⟩

lemma peel_at {X : Type*} [LinearOrder X] [Fintype X]
    (K : Finset (X → Bool)) (x : X) (b : Bool)
    (hag : Above K x) (hc : (side K x b).card = 1)
    (hK : 2 ≤ K.card) :
    ∃ z ∈ K,
      (∀ w ∈ K.erase z,
        w x ≠ z x ∧ ∀ y, x < y → w y = z y) ∧
      (K.erase z).Nonempty := by
  obtain ⟨z, he⟩ := Finset.card_eq_one.mp hc
  have hzS : z ∈ side K x b := by
    rw [he]
    exact Finset.mem_singleton_self z
  obtain ⟨hzK, hzb⟩ := (mem_side K x b z).mp hzS
  refine ⟨z, hzK, ?_, ?_⟩
  · intro w hw
    obtain ⟨hwz, hwK⟩ := Finset.mem_erase.mp hw
    refine ⟨?_, fun y hy => hag w hwK z hzK y hy⟩
    intro hwx
    have hwS : w ∈ side K x b :=
      (mem_side K x b w).mpr ⟨hwK, hwx.trans hzb⟩
    rw [he] at hwS
    exact hwz (Finset.mem_singleton.mp hwS)
  · apply Finset.card_pos.mp
    have := Finset.card_erase_of_mem hzK
    omega

lemma peel {X : Type*} [LinearOrder X] [Fintype X]
    (K : Finset (X → Bool)) (hcat : Cat K) (hK : 2 ≤ K.card) :
    ∃ x : X, ∃ z ∈ K,
      (∀ w ∈ K.erase z,
        w x ≠ z x ∧ ∀ y, x < y → w y = z y) ∧
      (K.erase z).Nonempty := by
  obtain ⟨x, hx⟩ := top K hK
  have hp := split_pos hx
  rcases cat_split hcat hx.1 with hf | ht
  · obtain ⟨z, hz, hr, hn⟩ :=
      peel_at K x false hx.1 (by omega) hK
    exact ⟨x, z, hz, hr, hn⟩
  · obtain ⟨z, hz, hr, hn⟩ :=
      peel_at K x true hx.1 (by omega) hK
    exact ⟨x, z, hz, hr, hn⟩

lemma above_insert {X : Type*} [LinearOrder X] [Fintype X]
    (z : X → Bool) (A : Finset (X → Bool)) (x : X)
    (hr : ∀ w ∈ A, ∀ y, x < y → w y = z y) :
    Above (insert z A) x := by
  have he : ∀ w ∈ insert z A, ∀ y, x < y → w y = z y := by
    intro w hw y hy
    rcases Finset.mem_insert.mp hw with hw | hw
    · rw [hw]
    · exact hr w hw y hy
  intro u hu v hv y hy
  exact (he u hu y hy).trans (he v hv y hy).symm

lemma cat_insert {X : Type*} [LinearOrder X] [Fintype X]
    (z : X → Bool) (A : Finset (X → Bool)) (x : X)
    (hr : ∀ w ∈ A, w x ≠ z x ∧ ∀ y, x < y → w y = z y)
    (hc : Cat A) : Cat (insert z A) := by
  intro B hB hBc hbal
  by_cases hzB : z ∈ B
  · obtain ⟨y, hag, hf, ht⟩ := hbal
    have hrestpos : 0 < (B.erase z).card := by
      have := Finset.card_erase_of_mem hzB
      omega
    obtain ⟨w, hw⟩ := Finset.card_pos.mp hrestpos
    obtain ⟨hwz, hwB⟩ := Finset.mem_erase.mp hw
    have hwA : w ∈ A := by
      rcases Finset.mem_insert.mp (hB hwB) with he | he
      · exact (hwz he).elim
      · exact he
    have hx : Split B x :=
      ⟨above_sub hB (above_insert z A x (fun v hv => (hr v hv).2)),
        w, hwB, z, hzB, (hr w hwA).1⟩
    have hy : Split B y := split_of_pos hag (by omega) (by omega)
    have hyx : y = x := split_unique hy hx
    subst y
    have hside : side B x (z x) ⊆ {z} := by
      intro v hv
      obtain ⟨hvB, hvx⟩ := (mem_side B x (z x) v).mp hv
      rcases Finset.mem_insert.mp (hB hvB) with he | he
      · exact Finset.mem_singleton.mpr he
      · exact ((hr v he).1 hvx).elim
    have hsidec : (side B x (z x)).card ≤ 1 := by
      simpa only [Finset.card_singleton] using Finset.card_le_card hside
    rcases bool_cases (z x) with he | he
    · rw [he] at hsidec
      omega
    · rw [he] at hsidec
      omega
  · have hBA : B ⊆ A := by
      intro v hv
      rcases Finset.mem_insert.mp (hB hv) with he | he
      · exact (hzB (he ▸ hv)).elim
      · exact he
    exact hc B hBA hBc hbal

noncomputable def levels {X : Type*} [LinearOrder X] [Fintype X]
    (A : Finset (X → Bool)) : Finset X :=
  Finset.univ.filter
    (fun x => ∃ u ∈ A, ∃ v ∈ A,
      u x ≠ v x ∧ ∀ y, x < y → u y = v y)

lemma mem_levels {X : Type*} [LinearOrder X] [Fintype X]
    (A : Finset (X → Bool)) (x : X) :
    x ∈ levels A ↔ ∃ u ∈ A, ∃ v ∈ A,
      u x ≠ v x ∧ ∀ y, x < y → u y = v y := by
  unfold levels
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ x, h⟩⟩

lemma levels_mono {X : Type*} [LinearOrder X] [Fintype X]
    {A B : Finset (X → Bool)} (hAB : A ⊆ B) :
    levels A ⊆ levels B := by
  intro x hx
  obtain ⟨u, hu, v, hv, h⟩ := (mem_levels A x).mp hx
  exact (mem_levels B x).mpr ⟨u, hAB hu, v, hAB hv, h⟩

lemma levels_singleton {X : Type*} [LinearOrder X] [Fintype X]
    (a : X → Bool) : levels ({a} : Finset (X → Bool)) = ∅ := by
  apply Finset.subset_empty.mp
  intro x hx
  obtain ⟨u, hu, v, hv, hne, _⟩ := (mem_levels {a} x).mp hx
  exact (hne (by
    rw [Finset.mem_singleton.mp hu, Finset.mem_singleton.mp hv])).elim

lemma level_unique {X : Type*} [LinearOrder X]
    (u v : X → Bool) (x y : X)
    (hx : u x ≠ v x) (hax : ∀ z, x < z → u z = v z)
    (hy : u y ≠ v y) (hay : ∀ z, y < z → u z = v z) :
    y = x := by
  rcases lt_trichotomy x y with h | h | h
  · exact (hy (hax y h)).elim
  · exact h.symm
  · exact (hx (hay x h)).elim

lemma levels_insert_sub {X : Type*} [LinearOrder X] [Fintype X]
    (z : X → Bool) (A : Finset (X → Bool)) (x : X)
    (hr : ∀ w ∈ A, w x ≠ z x ∧ ∀ y, x < y → w y = z y) :
    levels (insert z A) ⊆ insert x (levels A) := by
  intro y hy
  obtain ⟨u, hu, v, hv, hne, hag⟩ :=
    (mem_levels (insert z A) y).mp hy
  rcases Finset.mem_insert.mp hu with hu | hu
  · rcases Finset.mem_insert.mp hv with hv | hv
    · exact (hne (by rw [hu, hv])).elim
    · have hyx : y = x :=
        level_unique v z x y (hr v hv).1 (hr v hv).2
          (by rw [← hu]; exact fun h => hne h.symm)
          (by intro w hw; rw [← hu]; exact (hag w hw).symm)
      rw [hyx]
      exact Finset.mem_insert_self _ _
  · rcases Finset.mem_insert.mp hv with hv | hv
    · have hyx : y = x :=
        level_unique u z x y (hr u hu).1 (hr u hu).2
          (by rw [← hv]; exact hne)
          (by intro w hw; rw [← hv]; exact hag w hw)
      rw [hyx]
      exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem
        ((mem_levels A y).mpr ⟨u, hu, v, hv, hne, hag⟩)

lemma levels_insert_sup {X : Type*} [LinearOrder X] [Fintype X]
    (z : X → Bool) (A : Finset (X → Bool)) (x : X)
    (hr : ∀ w ∈ A, w x ≠ z x ∧ ∀ y, x < y → w y = z y)
    (hne : A.Nonempty) :
    insert x (levels A) ⊆ levels (insert z A) := by
  intro y hy
  rcases Finset.mem_insert.mp hy with hy | hy
  · obtain ⟨w, hw⟩ := hne
    rw [hy]
    exact (mem_levels (insert z A) x).mpr
      ⟨w, Finset.mem_insert_of_mem hw, z,
        Finset.mem_insert_self _ _, (hr w hw).1, (hr w hw).2⟩
  · exact levels_mono (Finset.subset_insert z A) hy

lemma level_not_mem {X : Type*} [LinearOrder X] [Fintype X]
    (z : X → Bool) (A : Finset (X → Bool)) (x : X)
    (hr : ∀ w ∈ A, w x ≠ z x ∧ ∀ y, x < y → w y = z y) :
    x ∉ levels A := by
  intro hx
  obtain ⟨u, hu, v, hv, hne, _⟩ := (mem_levels A x).mp hx
  exact hne (bool_eq (u x) (z x) (v x) (hr u hu).1 (hr v hv).1)

lemma levels_insert {X : Type*} [LinearOrder X] [Fintype X]
    (z : X → Bool) (A : Finset (X → Bool)) (x : X)
    (hr : ∀ w ∈ A, w x ≠ z x ∧ ∀ y, x < y → w y = z y)
    (hne : A.Nonempty) :
    levels (insert z A) = insert x (levels A) :=
  Finset.Subset.antisymm
    (levels_insert_sub z A x hr) (levels_insert_sup z A x hr hne)

lemma cat_card {X : Type*} [LinearOrder X] [Fintype X] :
    ∀ n : ℕ, ∀ A : Finset (X → Bool),
      A.card ≤ n → Cat A → A.card ≤ (levels A).card + 1 := by
  intro n
  induction n with
  | zero =>
      intro A hA _
      omega
  | succ n ih =>
      intro A hAn hc
      by_cases hsmall : A.card ≤ 1
      · omega
      obtain ⟨x, z, hz, hr, hne⟩ := peel A hc (by omega)
      have hs := levels_insert_sup z (A.erase z) x hr hne
      rw [Finset.insert_erase hz] at hs
      have hxn := level_not_mem z (A.erase z) x hr
      have he := Finset.card_erase_of_mem hz
      have hh := Finset.card_le_card hs
      rw [Finset.card_insert_of_notMem hxn] at hh
      have hi := ih (A.erase z) (by omega)
        (cat_sub (Finset.erase_subset z A) hc)
      omega

lemma realise {X : Type*} [LinearOrder X] [Fintype X] :
    ∀ n : ℕ, ∀ A : Finset (X → Bool),
      A.card ≤ n → Cat A → A.Nonempty →
      ∀ D : Finset X, D ⊆ levels A →
        ∃ B : Finset (X → Bool),
          B ⊆ A ∧ B.card = D.card + 1 ∧ levels B = D := by
  intro n
  induction n with
  | zero =>
      intro A hA _ hne D _
      have := Finset.card_pos.mpr hne
      omega
  | succ n ih =>
      intro A hAn hc hne D hD
      by_cases hDe : D = ∅
      · obtain ⟨z, hz⟩ := hne
        refine ⟨{z}, Finset.singleton_subset_iff.mpr hz, ?_, ?_⟩
        · simp [hDe]
        · rw [hDe]
          exact levels_singleton z
      obtain ⟨d, hd⟩ := Finset.nonempty_iff_ne_empty.mpr hDe
      obtain ⟨u, hu, v, hv, huv, _⟩ :=
        (mem_levels A d).mp (hD hd)
      have htwo : 2 ≤ A.card := by
        have hneuv : u ≠ v := fun h => huv (by rw [h])
        have hsub : ({u, v} : Finset (X → Bool)) ⊆ A :=
          Finset.insert_subset hu (Finset.singleton_subset_iff.mpr hv)
        have hh := Finset.card_le_card hsub
        rw [Finset.card_pair hneuv] at hh
        exact hh
      obtain ⟨x, z, hz, hr, hrest⟩ := peel A hc htwo
      have hcard : (A.erase z).card ≤ n := by
        have := Finset.card_erase_of_mem hz
        omega
      have hcat : Cat (A.erase z) :=
        cat_sub (Finset.erase_subset z A) hc
      have hsub : levels A ⊆ insert x (levels (A.erase z)) := by
        have hh := levels_insert_sub z (A.erase z) x hr
        rw [Finset.insert_erase hz] at hh
        exact hh
      by_cases hxD : x ∈ D
      · have hD' : D.erase x ⊆ levels (A.erase z) := by
          intro y hy
          obtain ⟨hyx, hyD⟩ := Finset.mem_erase.mp hy
          rcases Finset.mem_insert.mp (hsub (hD hyD)) with he | he
          · exact (hyx he).elim
          · exact he
        obtain ⟨B, hB, hBc, hBd⟩ :=
          ih (A.erase z) hcard hcat hrest (D.erase x) hD'
        have hzB : z ∉ B :=
          fun h => (Finset.mem_erase.mp (hB h)).1 rfl
        have hBn : B.Nonempty := Finset.card_pos.mp (by omega)
        refine ⟨insert z B,
          Finset.insert_subset hz
            (hB.trans (Finset.erase_subset z A)), ?_, ?_⟩
        · rw [Finset.card_insert_of_notMem hzB, hBc]
          have := Finset.card_erase_of_mem hxD
          have := Finset.card_pos.mpr ⟨x, hxD⟩
          omega
        · rw [levels_insert z B x
            (fun w hw => hr w (hB hw)) hBn, hBd]
          exact Finset.insert_erase hxD
      · have hD' : D ⊆ levels (A.erase z) := by
          intro y hy
          rcases Finset.mem_insert.mp (hsub (hD hy)) with he | he
          · exact (hxD (he ▸ hy)).elim
          · exact he
        obtain ⟨B, hB, hBc, hBd⟩ :=
          ih (A.erase z) hcard hcat hrest D hD'
        exact ⟨B, hB.trans (Finset.erase_subset z A), hBc, hBd⟩

def NC {X : Type*} [LinearOrder X] [Fintype X]
    (A : Finset (X → Bool)) : Prop :=
  ∃ w : X → Bool, Cat (A.erase w)

@[reducible] def JPart {X : Type*} [LinearOrder X] (t : ℕ)
    (P Q : Finset (X → Bool)) : Prop :=
  3 ≤ P.card ∧ P.card ≤ t ∧ ¬ Cat Q

def JSide {X : Type*} [LinearOrder X] (t : ℕ)
    (A : Finset (X → Bool)) : Prop :=
  ∃ x : X, Split A x ∧
    (JPart t (side A x false) (side A x true) ∨
      JPart t (side A x true) (side A x false))

noncomputable def colour {X C : Type*} [LinearOrder X] [Fintype X]
    (t : ℕ) (a b : C) (χ : Finset X → C) (A : Finset (X → Bool)) : C :=
  if Cat A then χ (levels A)
  else if NC A ∨ JSide t A then b else a

lemma colour_cat {X C : Type*} [LinearOrder X] [Fintype X] (t : ℕ)
    (a b : C) (χ : Finset X → C) (A : Finset (X → Bool)) (hc : Cat A) :
    colour t a b χ A = χ (levels A) := by
  unfold colour
  rw [if_pos hc]

lemma colour_b {X C : Type*} [LinearOrder X] [Fintype X] (t : ℕ)
    (a b : C) (χ : Finset X → C) (A : Finset (X → Bool)) (hc : ¬ Cat A)
    (h : NC A ∨ JSide t A) :
    colour t a b χ A = b := by
  unfold colour
  rw [if_neg hc, if_pos h]

lemma colour_a {X C : Type*} [LinearOrder X] [Fintype X] (t : ℕ)
    (a b : C) (χ : Finset X → C) (A : Finset (X → Bool)) (hc : ¬ Cat A)
    (h : ¬ (NC A ∨ JSide t A)) :
    colour t a b χ A = a := by
  unfold colour
  rw [if_neg hc, if_neg h]

lemma colour_noncat {X C : Type*} [LinearOrder X] [Fintype X] (t : ℕ)
    (a b : C) (χ : Finset X → C) (A : Finset (X → Bool)) (hc : ¬ Cat A) :
    colour t a b χ A = a ∨ colour t a b χ A = b := by
  by_cases h : NC A ∨ JSide t A
  · exact Or.inr (colour_b t a b χ A hc h)
  · exact Or.inl (colour_a t a b χ A hc h)

lemma nc_of_cat {X : Type*} [LinearOrder X] [Fintype X]
    {A : Finset (X → Bool)} (hc : Cat A) : NC A :=
  ⟨fun _ => false, cat_sub (Finset.erase_subset _ A) hc⟩

lemma nc_sub {X : Type*} [LinearOrder X] [Fintype X]
    {A B : Finset (X → Bool)} (hAB : A ⊆ B) (hB : NC B) : NC A := by
  obtain ⟨w, hw⟩ := hB
  exact ⟨w, cat_sub (Finset.erase_subset_erase w hAB) hw⟩

lemma nc_insert {X : Type*} [LinearOrder X] [Fintype X]
    (z : X → Bool) (A : Finset (X → Bool)) (x : X)
    (hr : ∀ w ∈ A, w x ≠ z x ∧ ∀ y, x < y → w y = z y)
    (hA : NC A) : NC (insert z A) := by
  obtain ⟨w, hw⟩ := hA
  refine ⟨w, cat_sub ?_
    (cat_insert z (A.erase w) x
      (fun v hv => hr v (Finset.mem_of_mem_erase hv)) hw)⟩
  intro v hv
  obtain ⟨hvw, hv'⟩ := Finset.mem_erase.mp hv
  rcases Finset.mem_insert.mp hv' with h | h
  · rw [h]
    exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hvw, h⟩)

lemma noncat_parts {X : Type*} [LinearOrder X] [Fintype X]
    (d : Bool) (A P Q : Finset (X → Bool)) (x : X)
    (hag : Above A x) (hPA : P ⊆ A) (hQA : Q ⊆ A)
    (hP : ∀ v ∈ P, v x = d) (hQ : ∀ v ∈ Q, v x ≠ d)
    (hPc : 2 ≤ P.card) (hQc : 2 ≤ Q.card) : ¬ Cat A := by
  intro hc
  have hs := cat_split hc hag
  cases d
  · have h1 : P ⊆ side A x false := fun v hv =>
      (mem_side A x false v).mpr ⟨hPA hv, hP v hv⟩
    have h2 : Q ⊆ side A x true := fun v hv =>
      (mem_side A x true v).mpr ⟨hQA hv, bool_ne_false _ (hQ v hv)⟩
    have e1 := Finset.card_le_card h1
    have e2 := Finset.card_le_card h2
    omega
  · have h1 : P ⊆ side A x true := fun v hv =>
      (mem_side A x true v).mpr ⟨hPA hv, hP v hv⟩
    have h2 : Q ⊆ side A x false := fun v hv =>
      (mem_side A x false v).mpr ⟨hQA hv, bool_ne_true _ (hQ v hv)⟩
    have e1 := Finset.card_le_card h1
    have e2 := Finset.card_le_card h2
    omega

lemma nonNC_three {X : Type*} [LinearOrder X] [Fintype X]
    (A P Q : Finset (X → Bool)) (x : X) (hag : Above A x)
    (hPA : P ⊆ A) (hQA : Q ⊆ A)
    (hP : ∀ v ∈ P, v x = false) (hQ : ∀ v ∈ Q, v x = true)
    (hPc : 3 ≤ P.card) (hQc : 3 ≤ Q.card) : ¬ NC A := by
  rintro ⟨w, hw⟩
  have h1 := card_erase_ge P w
  have h2 := card_erase_ge Q w
  exact noncat_parts false (A.erase w) (P.erase w) (Q.erase w) x
    (above_sub (Finset.erase_subset w A) hag)
    (Finset.erase_subset_erase w hPA) (Finset.erase_subset_erase w hQA)
    (fun v hv => hP v (Finset.mem_of_mem_erase hv))
    (fun v hv => by rw [hQ v (Finset.mem_of_mem_erase hv)]; decide)
    (by omega) (by omega) hw

lemma nonNC_gen {X : Type*} [LinearOrder X] [Fintype X]
    (d : Bool) (A P Q : Finset (X → Bool)) (x : X) (hag : Above A x)
    (hPA : P ⊆ A) (hQA : Q ⊆ A)
    (hP : ∀ v ∈ P, v x = d) (hQ : ∀ v ∈ Q, v x ≠ d)
    (hPc : 3 ≤ P.card) (hQc : 3 ≤ Q.card) : ¬ NC A := by
  rintro ⟨w, hw⟩
  have h1 := card_erase_ge P w
  have h2 := card_erase_ge Q w
  exact noncat_parts d (A.erase w) (P.erase w) (Q.erase w) x
    (above_sub (Finset.erase_subset w A) hag)
    (Finset.erase_subset_erase w hPA) (Finset.erase_subset_erase w hQA)
    (fun v hv => hP v (Finset.mem_of_mem_erase hv))
    (fun v hv => hQ v (Finset.mem_of_mem_erase hv))
    (by omega) (by omega) hw

lemma cover {X : Type*} [Fintype X] (K : Finset (X → Bool)) (x : X) :
    K ⊆ side K x false ∪ side K x true := by
  intro v hv
  rcases bool_cases (v x) with h | h
  · exact Finset.mem_union_left _ ((mem_side K x false v).mpr ⟨hv, h⟩)
  · exact Finset.mem_union_right _ ((mem_side K x true v).mpr ⟨hv, h⟩)

lemma disj_gen {X : Type*} (d : Bool) (x : X) (P Q : Finset (X → Bool))
    (hP : ∀ v ∈ P, v x = d) (hQ : ∀ v ∈ Q, v x ≠ d) : Disjoint P Q := by
  rw [Finset.disjoint_left]
  intro v hv hw
  exact hQ v hw (hP v hv)

lemma nc_two_side {X : Type*} [LinearOrder X] [Fintype X]
    (d : Bool) (S D E : Finset (X → Bool)) (x : X) (hag : Above S x)
    (hDS : D ⊆ S) (hES : E ⊆ S) (hD : ∀ v ∈ D, v x = d)
    (hE : ∀ v ∈ E, v x ≠ d) (hcov : S ⊆ D ∪ E)
    (hDc : D.card = 2) (hEc : 3 ≤ E.card)
    (hall : ∀ U : Finset (X → Bool), U ⊆ S → U.card ≤ 6 → NC U) :
    NC S := by
  obtain ⟨u, v, _, hDuv⟩ := Finset.card_eq_two.mp hDc
  have hv : v ∈ D := by
    rw [hDuv]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  by_cases hcE : Cat E
  · refine ⟨u, cat_sub ?_ (cat_insert v E x ?_ hcE)⟩
    · intro q hq
      obtain ⟨hqu, hqS⟩ := Finset.mem_erase.mp hq
      rcases Finset.mem_union.mp (hcov hqS) with h | h
      · rw [hDuv, Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with h | h
        · exact (hqu h).elim
        · rw [h]
          exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem h
    · intro w hw
      refine ⟨?_, fun y hy => hag w (hES hw) v (hDS hv) y hy⟩
      rw [hD v hv]
      exact hE w hw
  · exfalso
    obtain ⟨W, hW, hWc, hWb⟩ := bad_four E hcE
    have hUS : W ∪ D ⊆ S := Finset.union_subset (hW.trans hES) hDS
    have hUc : (W ∪ D).card ≤ 6 := by
      have := Finset.card_union_le W D
      omega
    obtain ⟨w, hw⟩ := hall (W ∪ D) hUS hUc
    have hag' : Above ((W ∪ D).erase w) x :=
      above_sub ((Finset.erase_subset w _).trans hUS) hag
    by_cases hwW : w ∈ W
    · have hsubD : D ⊆ (W ∪ D).erase w := by
        intro q hq
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_union_right _ hq⟩
        intro hqw
        rw [hqw] at hq
        exact hE w (hW hwW) (hD w hq)
      have hsubW : W.erase w ⊆ (W ∪ D).erase w :=
        Finset.erase_subset_erase w Finset.subset_union_left
      have hWd : ∀ q ∈ W.erase w, q x ≠ d :=
        fun q hq => hE q (hW (Finset.mem_of_mem_erase hq))
      have hWe := card_erase_ge W w
      exact noncat_parts d ((W ∪ D).erase w) D (W.erase w) x hag'
        hsubD hsubW hD hWd (by omega) (by omega) hw
    · have hsub : W ⊆ (W ∪ D).erase w := fun q hq =>
        Finset.mem_erase.mpr
          ⟨fun h => hwW (by rw [← h]; exact hq), Finset.mem_union_left _ hq⟩
      exact hw W hsub hWc hWb

lemma nc_local {X : Type*} [LinearOrder X] [Fintype X] :
    ∀ n : ℕ, ∀ S : Finset (X → Bool), S.card ≤ n →
      (∀ U : Finset (X → Bool), U ⊆ S → U.card ≤ 6 → NC U) → NC S := by
  intro n
  induction n with
  | zero =>
      intro S hS hall
      exact hall S (Finset.Subset.refl S) (by omega)
  | succ n ih =>
      intro S hSn hall
      by_cases hsmall : S.card ≤ 6
      · exact hall S (Finset.Subset.refl S) hsmall
      obtain ⟨x, hx⟩ := top S (by omega)
      obtain ⟨hp1, hp2⟩ := split_pos hx
      have hsum := side_card_sum S x
      have hsub : ∀ z ∈ S, NC (S.erase z) := fun z hz =>
        ih (S.erase z) (by have := Finset.card_erase_lt_of_mem hz; omega)
          (fun U hU hUc => hall U (hU.trans (Finset.erase_subset z S)) hUc)
      by_cases hf1 : (side S x false).card ≤ 1
      · obtain ⟨z, hz, hr, _⟩ := peel_at S x false hx.1 (by omega) (by omega)
        have h2 := nc_insert z (S.erase z) x hr (hsub z hz)
        rwa [Finset.insert_erase hz] at h2
      by_cases ht1 : (side S x true).card ≤ 1
      · obtain ⟨z, hz, hr, _⟩ := peel_at S x true hx.1 (by omega) (by omega)
        have h2 := nc_insert z (S.erase z) x hr (hsub z hz)
        rwa [Finset.insert_erase hz] at h2
      by_cases hf2 : (side S x false).card = 2
      · exact nc_two_side false S (side S x false) (side S x true) x hx.1
          (side_subset S x false) (side_subset S x true)
          (fun v hv => ((mem_side S x false v).mp hv).2)
          (fun v hv => by rw [((mem_side S x true v).mp hv).2]; decide)
          (cover S x) hf2 (by omega) hall
      by_cases ht2 : (side S x true).card = 2
      · exact nc_two_side true S (side S x true) (side S x false) x hx.1
          (side_subset S x true) (side_subset S x false)
          (fun v hv => ((mem_side S x true v).mp hv).2)
          (fun v hv => by rw [((mem_side S x false v).mp hv).2]; decide)
          (by rw [Finset.union_comm]; exact cover S x) ht2 (by omega) hall
      exfalso
      obtain ⟨P, hPS, hPc, hP⟩ := choose_side S x false 3 (by omega)
      obtain ⟨Q, hQS, hQc, hQ⟩ := choose_side S x true 3 (by omega)
      have hUS : P ∪ Q ⊆ S := Finset.union_subset hPS hQS
      have hUc : (P ∪ Q).card ≤ 6 := by
        have := Finset.card_union_le P Q
        omega
      exact nonNC_three (P ∪ Q) P Q x (above_sub hUS hx.1)
        Finset.subset_union_left Finset.subset_union_right hP hQ
        (by omega) (by omega) (hall (P ∪ Q) hUS hUc)

lemma sides_gen {X : Type*} [Fintype X] (d : Bool) (x : X)
    (D E : Finset (X → Bool))
    (hD : ∀ v ∈ D, v x = d) (hE : ∀ v ∈ E, v x ≠ d) :
    (side (D ∪ E) x false = D ∧ side (D ∪ E) x true = E) ∨
    (side (D ∪ E) x false = E ∧ side (D ∪ E) x true = D) := by
  cases d
  · exact Or.inl (sides_union x D E hD (fun v hv => bool_ne_false _ (hE v hv)))
  · right
    rw [Finset.union_comm D E]
    exact sides_union x E D (fun v hv => bool_ne_true _ (hE v hv)) hD

lemma split_parts {X : Type*} [LinearOrder X] [Fintype X] (d : Bool) (x : X)
    (D E : Finset (X → Bool))
    (hag : Above (D ∪ E) x) (hD : ∀ v ∈ D, v x = d) (hE : ∀ v ∈ E, v x ≠ d)
    (hDn : 0 < D.card) (hEn : 0 < E.card) : Split (D ∪ E) x := by
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hDn
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hEn
  exact ⟨hag, u, Finset.mem_union_left _ hu, v, Finset.mem_union_right _ hv,
    fun h => hE v hv (h.symm.trans (hD u hu))⟩

lemma jside_parts {X : Type*} [LinearOrder X] [Fintype X] (t : ℕ) (d : Bool)
    (x : X) (D E : Finset (X → Bool)) (hs : Split (D ∪ E) x)
    (hD : ∀ v ∈ D, v x = d) (hE : ∀ v ∈ E, v x ≠ d) :
    JSide t (D ∪ E) ↔ (JPart t D E ∨ JPart t E D) := by
  constructor
  · rintro ⟨y, hy, h⟩
    have hxy := split_unique hs hy
    rw [← hxy] at h
    rcases sides_gen d x D E hD hE with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2] at h
      exact h
    · rw [h1, h2] at h
      exact h.symm
  · intro h
    refine ⟨x, hs, ?_⟩
    rcases sides_gen d x D E hD hE with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
      exact h
    · rw [h1, h2]
      exact h.symm

lemma colour_parts_a {X C : Type*} [LinearOrder X] [Fintype X] (t : ℕ)
    (a b : C) (χ : Finset X → C) (d : Bool) (x : X) (D E : Finset (X → Bool))
    (hag : Above (D ∪ E) x) (hD : ∀ v ∈ D, v x = d) (hE : ∀ v ∈ E, v x ≠ d)
    (hDn : 0 < D.card) (hEn : 0 < E.card)
    (h1 : ¬ JPart t D E) (h2 : ¬ JPart t E D) (hnc : ¬ NC (D ∪ E)) :
    colour t a b χ (D ∪ E) = a := by
  have hs := split_parts d x D E hag hD hE hDn hEn
  apply colour_a t a b χ (D ∪ E) (fun hc => hnc (nc_of_cat hc))
  rintro (h | h)
  · exact hnc h
  · rcases (jside_parts t d x D E hs hD hE).mp h with h' | h'
    · exact h1 h'
    · exact h2 h'

lemma colour_parts_b {X C : Type*} [LinearOrder X] [Fintype X] (t : ℕ)
    (a b : C) (χ : Finset X → C) (d : Bool) (x : X) (D E : Finset (X → Bool))
    (hag : Above (D ∪ E) x) (hD : ∀ v ∈ D, v x = d) (hE : ∀ v ∈ E, v x ≠ d)
    (hDn : 0 < D.card) (hEn : 0 < E.card)
    (hj : JPart t D E) (hnc : ¬ Cat (D ∪ E)) :
    colour t a b χ (D ∪ E) = b := by
  have hs := split_parts d x D E hag hD hE hDn hEn
  exact colour_b t a b χ (D ∪ E) hnc
    (Or.inr ((jside_parts t d x D E hs hD hE).mpr (Or.inl hj)))

lemma cat_bound {X C : Type*} [LinearOrder X] [Fintype X]
    (k s t : ℕ) (a b : C) (χ : Finset X → C) (i : C)
    (hχ : Solon.NoMono χ k s i)
    (K : Finset (X → Bool))
    (hm : ∀ A : Finset (X → Bool), A ⊆ K → A.card = k + 1 → colour t a b χ A = i)
    (D : Finset (X → Bool)) (hDK : D ⊆ K) (hc : Cat D) :
    D.card ≤ s := by
  by_contra hbig
  have hh := cat_card D.card D (le_refl _) hc
  obtain ⟨S, hS, hSc⟩ :=
    Finset.exists_subset_card_eq (show s ≤ (levels D).card by omega)
  obtain ⟨T, hT, hne⟩ := hχ S hSc
  obtain ⟨hTS, hTc⟩ := Finset.mem_powersetCard.mp hT
  have hDn : D.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨A, hAD, hAc, hAt⟩ :=
    realise D.card D (le_refl _) hc hDn T (hTS.trans hS)
  have hcol := hm A (hAD.trans hDK) (by omega)
  rw [colour_cat t a b χ A (cat_sub hAD hc), hAt] at hcol
  exact hne hcol

lemma cat_local {X : Type*} [LinearOrder X] [Fintype X] (m : ℕ) (hm : 4 ≤ m)
    (K : Finset (X → Bool)) (hKm : m ≤ K.card)
    (hall : ∀ A : Finset (X → Bool), A ⊆ K → A.card = m → Cat A) : Cat K := by
  intro B hB hBc hbal
  obtain ⟨A, hBA, hAK, hAc⟩ := extend B K m hB (by omega) hKm
  exact hall A hAK hAc B hBA hBc hbal

lemma nc_witness {X : Type*} [LinearOrder X] [Fintype X]
    (k : ℕ) (hk : 3 ≤ k) (K T : Finset (X → Bool)) (hTK : T ⊆ K)
    (hcT : Cat T) (hTc : k ≤ T.card) (hK : ¬ Cat K) :
    ∃ A : Finset (X → Bool), A ⊆ K ∧ A.card = k + 1 ∧ ¬ Cat A ∧ NC A := by
  have hmem : T ∈ K.powerset.filter Cat :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hTK, hcT⟩
  obtain ⟨M, hM, hmax⟩ :=
    Finset.exists_max_image (K.powerset.filter Cat) Finset.card ⟨T, hmem⟩
  obtain ⟨hMK', hcM⟩ := Finset.mem_filter.mp hM
  have hMK : M ⊆ K := Finset.mem_powerset.mp hMK'
  have hTM := hmax T hmem
  have hne : ∃ p ∈ K, p ∉ M := by
    by_contra h
    apply hK
    have hKM : K ⊆ M := by
      intro v hv
      by_contra hvM
      exact h ⟨v, hv, hvM⟩
    have he : K = M := Finset.Subset.antisymm hKM hMK
    rw [he]
    exact hcM
  obtain ⟨p, hpK, hpM⟩ := hne
  have hncat : ¬ Cat (insert p M) := by
    intro hc
    have h1 := hmax (insert p M)
      (Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr (Finset.insert_subset hpK hMK), hc⟩)
    rw [Finset.card_insert_of_notMem hpM] at h1
    omega
  obtain ⟨W, hW, hWc, hWb⟩ := bad_four (insert p M) hncat
  have hpW : p ∈ W := by
    by_contra hpW
    have hWM : W ⊆ M := by
      intro v hv
      rcases Finset.mem_insert.mp (hW hv) with h | h
      · rw [h] at hv
        exact (hpW hv).elim
      · exact h
    exact hcM W hWM hWc hWb
  have hWe : W.erase p ⊆ M := by
    intro v hv
    obtain ⟨hvp, hvW⟩ := Finset.mem_erase.mp hv
    rcases Finset.mem_insert.mp (hW hvW) with h | h
    · exact (hvp h).elim
    · exact h
  have hWec : (W.erase p).card = 3 := by
    rw [Finset.card_erase_of_mem hpW, hWc]
  obtain ⟨M', hWM', hM'M, hM'c⟩ := extend (W.erase p) M k hWe (by omega) (by omega)
  have hpM' : p ∉ M' := fun h => hpM (hM'M h)
  refine ⟨insert p M', Finset.insert_subset hpK (hM'M.trans hMK), ?_, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem hpM', hM'c]
  · intro hc
    have hWA : W ⊆ insert p M' := by
      intro v hv
      by_cases hvp : v = p
      · rw [hvp]
        exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hWM' (Finset.mem_erase.mpr ⟨hvp, hv⟩))
    exact hc W hWA hWc hWb
  · refine ⟨p, cat_sub ?_ hcM⟩
    intro v hv
    obtain ⟨hvp, hv'⟩ := Finset.mem_erase.mp hv
    rcases Finset.mem_insert.mp hv' with h | h
    · exact (hvp h).elim
    · exact hM'M h

lemma attach {X : Type*} [LinearOrder X] [Fintype X]
    (K : Finset (X → Bool)) (x : X) (hag : Above K x) (d : Bool)
    (z : X → Bool) (hz : z ∈ K) (hzd : z x ≠ d)
    (T : Finset (X → Bool)) (hT : T ⊆ K) (hTd : ∀ v ∈ T, v x = d) (hc : Cat T) :
    ∃ D : Finset (X → Bool), D ⊆ K ∧ Cat D ∧ D.card = T.card + 1 := by
  have hzT : z ∉ T := fun h => hzd (hTd z h)
  have hr : ∀ w ∈ T, w x ≠ z x ∧ ∀ y, x < y → w y = z y := by
    intro w hw
    refine ⟨?_, fun y hy => hag w (hT hw) z hz y hy⟩
    intro he
    exact hzd (he.symm.trans (hTd w hw))
  exact ⟨insert z T, Finset.insert_subset hz hT, cat_insert z T x hr hc,
    Finset.card_insert_of_notMem hzT⟩

lemma side_cat {X C : Type*} [LinearOrder X] [Fintype X]
    (k t : ℕ) (ht3 : 3 ≤ t) (htk : 2 * t + 1 ≤ k) (a b : C) (hab : a ≠ b)
    (χ : Finset X → C) (d : Bool)
    (K D E : Finset (X → Bool)) (x : X) (hag : Above K x)
    (hDK : D ⊆ K) (hEK : E ⊆ K) (hD : ∀ v ∈ D, v x = d)
    (hE : ∀ v ∈ E, v x ≠ d) (h2 : D.card = 2) (hEc : k - 1 ≤ E.card)
    (hm : ∀ A : Finset (X → Bool), A ⊆ K → A.card = k + 1 →
      colour t a b χ A = b) : Cat E := by
  apply cat_local (k - 1) (by omega) E hEc
  intro E' hE'E hE'c
  by_contra hcE'
  have hsub : D ∪ E' ⊆ K := Finset.union_subset hDK (hE'E.trans hEK)
  have hE'd : ∀ w ∈ E', w x ≠ d := fun w hw => hE w (hE'E hw)
  have hnc : ¬ NC (D ∪ E') := by
    rintro ⟨w, hw⟩
    by_cases hwE : w ∈ E'
    · have hsubD : D ⊆ (D ∪ E').erase w := by
        intro q hq
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_union_left _ hq⟩
        intro hqw
        rw [hqw] at hq
        exact hE'd w hwE (hD w hq)
      have hsubE : E'.erase w ⊆ (D ∪ E').erase w :=
        Finset.erase_subset_erase w Finset.subset_union_right
      have hEd' : ∀ q ∈ E'.erase w, q x ≠ d :=
        fun q hq => hE'd q (Finset.mem_of_mem_erase hq)
      have hce := card_erase_ge E' w
      exact noncat_parts d ((D ∪ E').erase w) D (E'.erase w) x
        (above_sub ((Finset.erase_subset w _).trans hsub) hag)
        hsubD hsubE hD hEd' (by omega) (by omega) hw
    · have hsubE : E' ⊆ (D ∪ E').erase w := fun q hq =>
        Finset.mem_erase.mpr
          ⟨fun h => hwE (by rw [← h]; exact hq), Finset.mem_union_right _ hq⟩
      exact hcE' (cat_sub hsubE hw)
  have hc : (D ∪ E').card = k + 1 := by
    rw [Finset.card_union_of_disjoint (disj_gen d x D E' hD hE'd), h2, hE'c]
    omega
  have hcol := colour_parts_a t a b χ d x D E' (above_sub hsub hag) hD hE'd
    (by omega) (by omega) (fun h => by obtain ⟨hh, _, _⟩ := h; omega)
    (fun h => by obtain ⟨_, hh, _⟩ := h; omega) hnc
  exact hab (hcol.symm.trans (hm _ hsub hc))

lemma b_thin {X C : Type*} [LinearOrder X] [Fintype X]
    (k t : ℕ) (ht3 : 3 ≤ t) (htk : 2 * t + 1 ≤ k) (a b : C) (hab : a ≠ b)
    (χ : Finset X → C) (d : Bool)
    (K D E : Finset (X → Bool)) (x : X) (hag : Above K x)
    (hDK : D ⊆ K) (hEK : E ⊆ K) (hD : ∀ v ∈ D, v x = d)
    (hE : ∀ v ∈ E, v x ≠ d)
    (hcov : K ⊆ D ∪ E) (hDc : D.card = 1 ∨ D.card = 2) (hEc : k ≤ E.card)
    (hm : ∀ A : Finset (X → Bool), A ⊆ K → A.card = k + 1 →
      colour t a b χ A = b) : NC K := by
  rcases hDc with h1 | h2
  · obtain ⟨p, hpD⟩ := Finset.card_eq_one.mp h1
    have hp : p ∈ D := by
      rw [hpD]
      exact Finset.mem_singleton_self p
    have hNE : NC E := by
      apply nc_local E.card E (le_refl _)
      intro U hUE hUc
      by_contra hU
      obtain ⟨E', hUE', hE'E, hE'c⟩ := extend U E k hUE (by omega) hEc
      have hsub : D ∪ E' ⊆ K := Finset.union_subset hDK (hE'E.trans hEK)
      have hE'd : ∀ v ∈ E', v x ≠ d := fun v hv => hE v (hE'E hv)
      have hnc : ¬ NC (D ∪ E') := fun h =>
        hU (nc_sub (hUE'.trans Finset.subset_union_right) h)
      have hcol := colour_parts_a t a b χ d x D E' (above_sub hsub hag) hD hE'd
        (by omega) (by omega) (fun h => by obtain ⟨hh, _, _⟩ := h; omega)
        (fun h => by obtain ⟨_, hh, _⟩ := h; omega) hnc
      have hc : (D ∪ E').card = k + 1 := by
        rw [Finset.card_union_of_disjoint (disj_gen d x D E' hD hE'd), h1, hE'c]
        omega
      exact hab (hcol.symm.trans (hm _ hsub hc))
    have hK : K ⊆ insert p E := by
      intro w hw
      rcases Finset.mem_union.mp (hcov hw) with h | h
      · rw [hpD, Finset.mem_singleton] at h
        rw [h]
        exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem h
    have hr : ∀ w ∈ E, w x ≠ p x ∧ ∀ y, x < y → w y = p y := fun w hw =>
      ⟨by rw [hD p hp]; exact hE w hw, fun y hy => hag w (hEK hw) p (hDK hp) y hy⟩
    exact nc_sub hK (nc_insert p E x hr hNE)
  · obtain ⟨u, v, _, hDuv⟩ := Finset.card_eq_two.mp h2
    have hv : v ∈ D := by
      rw [hDuv]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hcE : Cat E := side_cat k t ht3 htk a b hab χ d K D E x hag hDK hEK hD hE
      h2 (by omega) hm
    refine ⟨u, cat_sub ?_ (cat_insert v E x ?_ hcE)⟩
    · intro q hq
      obtain ⟨hqu, hqK⟩ := Finset.mem_erase.mp hq
      rcases Finset.mem_union.mp (hcov hqK) with h | h
      · rw [hDuv, Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with h | h
        · exact (hqu h).elim
        · rw [h]
          exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem h
    · intro w hw
      refine ⟨?_, fun y hy => hag w (hEK hw) v (hDK hv) y hy⟩
      rw [hD v hv]
      exact hE w hw

lemma big_side {X C : Type*} [LinearOrder X] [Fintype X]
    (k t : ℕ) (ht3 : 3 ≤ t) (htk : 2 * t + 1 ≤ k) (a b : C) (hab : a ≠ b)
    (χ : Finset X → C) (d : Bool)
    (K D E : Finset (X → Bool)) (x : X) (hag : Above K x)
    (hDK : D ⊆ K) (hEK : E ⊆ K) (hD : ∀ v ∈ D, v x = d)
    (hE : ∀ v ∈ E, v x ≠ d) (hDc : 3 ≤ D.card) (hEc : k - 1 ≤ E.card)
    (hm : ∀ A : Finset (X → Bool), A ⊆ K → A.card = k + 1 →
      colour t a b χ A = b) : False := by
  obtain ⟨D2, hD2, hD2c⟩ := Finset.exists_subset_card_eq (show 2 ≤ D.card by omega)
  have hcE := side_cat k t ht3 htk a b hab χ d K D2 E x hag (hD2.trans hDK) hEK
    (fun v hv => hD v (hD2 hv)) hE hD2c hEc hm
  obtain ⟨P, hP, hPc⟩ := Finset.exists_subset_card_eq hDc
  obtain ⟨Q, hQ, hQc⟩ := Finset.exists_subset_card_eq (show k - 2 ≤ E.card by omega)
  have hPd : ∀ v ∈ P, v x = d := fun v hv => hD v (hP hv)
  have hQd : ∀ v ∈ Q, v x ≠ d := fun v hv => hE v (hQ hv)
  have hsub : P ∪ Q ⊆ K := Finset.union_subset (hP.trans hDK) (hQ.trans hEK)
  have hc : (P ∪ Q).card = k + 1 := by
    rw [Finset.card_union_of_disjoint (disj_gen d x P Q hPd hQd), hPc, hQc]
    omega
  have hag' : Above (P ∪ Q) x := above_sub hsub hag
  have hnc : ¬ NC (P ∪ Q) :=
    nonNC_gen d (P ∪ Q) P Q x hag' Finset.subset_union_left Finset.subset_union_right
      hPd hQd (by omega) (by omega)
  have hcol := colour_parts_a t a b χ d x P Q hag' hPd hQd (by omega) (by omega)
    (fun h => by obtain ⟨_, _, h3⟩ := h; exact h3 (cat_sub hQ hcE))
    (fun h => by obtain ⟨_, h2, _⟩ := h; omega) hnc
  exact hab (hcol.symm.trans (hm _ hsub hc))

lemma b_main {X C : Type*} [LinearOrder X] [Fintype X]
    (k t : ℕ) (ht3 : 3 ≤ t) (htk : 2 * t + 1 ≤ k) (a b : C) (hab : a ≠ b)
    (χ : Finset X → C)
    (K : Finset (X → Bool)) (hK : k + t - 1 ≤ K.card)
    (hm : ∀ A : Finset (X → Bool), A ⊆ K → A.card = k + 1 →
      colour t a b χ A = b)
    (hnc : ¬ NC K) : False := by
  obtain ⟨x, hx⟩ := top K (by omega)
  obtain ⟨hp1, hp2⟩ := split_pos hx
  have hsum := side_card_sum K x
  by_cases hl : (side K x false).card ≤ 2
  · exact hnc (b_thin k t ht3 htk a b hab χ false K (side K x false) (side K x true) x hx.1
      (side_subset K x false) (side_subset K x true)
      (fun v hv => ((mem_side K x false v).mp hv).2)
      (fun v hv => by rw [((mem_side K x true v).mp hv).2]; decide)
      (cover K x) (by omega) (by omega) hm)
  by_cases hr : (side K x true).card ≤ 2
  · exact hnc (b_thin k t ht3 htk a b hab χ true K (side K x true) (side K x false) x hx.1
      (side_subset K x true) (side_subset K x false)
      (fun v hv => ((mem_side K x true v).mp hv).2)
      (fun v hv => by rw [((mem_side K x false v).mp hv).2]; decide)
      (by rw [Finset.union_comm]; exact cover K x) (by omega) (by omega) hm)
  have hF : ∀ v ∈ side K x false, v x = false :=
    fun v hv => ((mem_side K x false v).mp hv).2
  have hT : ∀ v ∈ side K x true, v x = true :=
    fun v hv => ((mem_side K x true v).mp hv).2
  have hFn : ∀ v ∈ side K x false, v x ≠ true := fun v hv => by rw [hF v hv]; decide
  have hTn : ∀ v ∈ side K x true, v x ≠ false := fun v hv => by rw [hT v hv]; decide
  by_cases hbigT : k - 1 ≤ (side K x true).card
  · exact big_side k t ht3 htk a b hab χ false K (side K x false) (side K x true) x hx.1
      (side_subset K x false) (side_subset K x true) hF hTn (by omega) hbigT hm
  by_cases hbigF : k - 1 ≤ (side K x false).card
  · exact big_side k t ht3 htk a b hab χ true K (side K x true) (side K x false) x hx.1
      (side_subset K x true) (side_subset K x false) hT hFn (by omega) hbigF hm
  by_cases hsmall : (side K x false).card ≤ t ∨ (side K x true).card ≤ t
  · omega
  obtain ⟨hs1, hs2⟩ := not_or.mp hsmall
  obtain ⟨r, hr1, hr2, hr3, hr4⟩ : ∃ r : ℕ, t + 1 ≤ r ∧ r ≤ (side K x false).card ∧
      t + 1 ≤ k + 1 - r ∧ k + 1 - r ≤ (side K x true).card := by
    by_cases hc : k + 1 - (side K x true).card ≤ t + 1
    · exact ⟨t + 1, le_refl _, by omega, by omega, by omega⟩
    · exact ⟨k + 1 - (side K x true).card, by omega, by omega, by omega, by omega⟩
  obtain ⟨P, hPK, hPc, hP⟩ := choose_side K x false r hr2
  obtain ⟨Q, hQK, hQc, hQ⟩ := choose_side K x true (k + 1 - r) hr4
  have hQn : ∀ v ∈ Q, v x ≠ false := fun v hv => by rw [hQ v hv]; decide
  have hAK : P ∪ Q ⊆ K := Finset.union_subset hPK hQK
  have hAc : (P ∪ Q).card = k + 1 := by
    rw [Finset.card_union_of_disjoint (bits_disjoint x P Q hP hQ), hPc, hQc]
    omega
  have hag : Above (P ∪ Q) x := above_sub hAK hx.1
  have hAnc : ¬ NC (P ∪ Q) :=
    nonNC_gen false (P ∪ Q) P Q x hag Finset.subset_union_left
      Finset.subset_union_right hP hQn (by omega) (by omega)
  have h1 := colour_parts_a t a b χ false x P Q hag hP hQn (by omega) (by omega)
    (fun h => by obtain ⟨_, hj, _⟩ := h; omega)
    (fun h => by obtain ⟨_, hj, _⟩ := h; omega) hAnc
  exact hab (h1.symm.trans (hm (P ∪ Q) hAK hAc))

lemma mono_b {X C : Type*} [LinearOrder X] [Fintype X]
    (k t : ℕ) (ht3 : 3 ≤ t) (htk : 2 * t + 1 ≤ k) (a b : C) (hab : a ≠ b)
    (χ : Finset X → C) (s : ℕ) (hχ : Solon.NoMono χ k s b) :
    Solon.NoMono (colour t a b χ) (k + 1) (max (s + 2) (k + t - 1)) b := by
  intro K hK
  by_contra hn
  have hm : ∀ A : Finset (X → Bool), A ⊆ K → A.card = k + 1 →
      colour t a b χ A = b := by
    intro A hA hc
    by_contra hne
    exact hn ⟨A, Finset.mem_powersetCard.mpr ⟨hA, hc⟩, hne⟩
  have hK1 : s + 2 ≤ K.card := by
    rw [hK]
    exact le_max_left _ _
  have hK2 : k + t - 1 ≤ K.card := by
    rw [hK]
    exact le_max_right _ _
  by_cases hnc : NC K
  · obtain ⟨w, hw⟩ := hnc
    have h1 := cat_bound k s t a b χ b hχ K hm (K.erase w) (Finset.erase_subset w K) hw
    have h2 := card_erase_ge K w
    omega
  · exact b_main k t ht3 htk a b hab χ K hK2 hm hnc

lemma noncat_bound {X C : Type*} [LinearOrder X] [Fintype X]
    (k t : ℕ) (ht3 : 3 ≤ t) (htk : 2 * t + 1 ≤ k) (a b : C) (hab : a ≠ b)
    (χ : Finset X → C) (d : Bool)
    (K D E : Finset (X → Bool)) (x : X) (hag : Above K x)
    (hDK : D ⊆ K) (hEK : E ⊆ K) (hD : ∀ v ∈ D, v x = d)
    (hE : ∀ v ∈ E, v x ≠ d) (j : ℕ) (hj3 : 3 ≤ j) (hjt : j ≤ t) (hjD : j ≤ D.card)
    (hEnc : ¬ Cat E)
    (hm : ∀ A : Finset (X → Bool), A ⊆ K → A.card = k + 1 →
      colour t a b χ A = a) : E.card + j ≤ k := by
  by_contra hbig
  obtain ⟨P, hP, hPc⟩ := Finset.exists_subset_card_eq hjD
  obtain ⟨W, hW, hWc, hWb⟩ := bad_four E hEnc
  obtain ⟨Q, hWQ, hQE, hQc⟩ := extend W E (k + 1 - j) hW (by omega) (by omega)
  have hPd : ∀ v ∈ P, v x = d := fun v hv => hD v (hP hv)
  have hQd : ∀ v ∈ Q, v x ≠ d := fun v hv => hE v (hQE hv)
  have hsub : P ∪ Q ⊆ K := Finset.union_subset (hP.trans hDK) (hQE.trans hEK)
  have hc : (P ∪ Q).card = k + 1 := by
    rw [Finset.card_union_of_disjoint (disj_gen d x P Q hPd hQd), hPc, hQc]
    omega
  have hQnc : ¬ Cat Q := fun h => h W hWQ hWc hWb
  have hAnc : ¬ Cat (P ∪ Q) := fun h => hQnc (cat_sub Finset.subset_union_right h)
  have hcol := colour_parts_b t a b χ d x P Q (above_sub hsub hag) hPd hQd
    (by omega) (by omega) ⟨by omega, by omega, hQnc⟩ hAnc
  exact hab ((hm _ hsub hc).symm.trans hcol)

lemma noncat_bound' {X C : Type*} [LinearOrder X] [Fintype X]
    (k t : ℕ) (ht3 : 3 ≤ t) (htk : 2 * t + 1 ≤ k) (a b : C) (hab : a ≠ b)
    (χ : Finset X → C) (d : Bool)
    (K D E : Finset (X → Bool)) (x : X) (hag : Above K x)
    (hDK : D ⊆ K) (hEK : E ⊆ K) (hD : ∀ v ∈ D, v x = d)
    (hE : ∀ v ∈ E, v x ≠ d) (hDc : 3 ≤ D.card) (hEnc : ¬ Cat E)
    (hm : ∀ A : Finset (X → Bool), A ⊆ K → A.card = k + 1 →
      colour t a b χ A = a) :
    E.card + D.card ≤ k ∨ (t < D.card ∧ E.card + t ≤ k) := by
  by_cases hlt : D.card ≤ t
  · exact Or.inl (noncat_bound k t ht3 htk a b hab χ d K D E x hag hDK hEK hD hE
      D.card hDc hlt (le_refl _) hEnc hm)
  · exact Or.inr ⟨by omega, noncat_bound k t ht3 htk a b hab χ d K D E x hag hDK hEK
      hD hE t ht3 (le_refl _) (by omega) hEnc hm⟩

lemma extract {X C : Type*} [LinearOrder X] [Fintype X]
    (k t : ℕ) (ht3 : 3 ≤ t) (htk : 2 * t + 1 ≤ k) (a b : C) (hab : a ≠ b)
    (χ : Finset X → C) :
    ∀ n : ℕ, ∀ K : Finset (X → Bool), K.card ≤ n →
      (∀ A : Finset (X → Bool), A ⊆ K → A.card = k + 1 → colour t a b χ A = a) →
      ∃ T : Finset (X → Bool), T ⊆ K ∧ Cat T ∧
        K.card ≤ 2 * T.card + (2 * k - 2 * t - 8) := by
  intro n
  induction n with
  | zero =>
      intro K hK _
      refine ⟨∅, Finset.empty_subset K, cat_small ∅ (by simp), ?_⟩
      rw [Finset.card_empty]
      omega
  | succ n ih =>
      intro K hKn hm
      by_cases hsmall : K.card ≤ 3
      · exact ⟨K, Finset.Subset.refl K, cat_small K hsmall, by omega⟩
      obtain ⟨x, hx⟩ := top K (by omega)
      obtain ⟨hp1, hp2⟩ := split_pos hx
      have hsum := side_card_sum K x
      have hF : ∀ v ∈ side K x false, v x = false :=
        fun v hv => ((mem_side K x false v).mp hv).2
      have hT : ∀ v ∈ side K x true, v x = true :=
        fun v hv => ((mem_side K x true v).mp hv).2
      have hFn : ∀ v ∈ side K x false, v x ≠ true := fun v hv => by rw [hF v hv]; decide
      have hTn : ∀ v ∈ side K x true, v x ≠ false := fun v hv => by rw [hT v hv]; decide
      obtain ⟨zf, hzf⟩ := Finset.card_pos.mp hp1
      obtain ⟨hzfK, hzff⟩ := (mem_side K x false zf).mp hzf
      obtain ⟨zt, hzt⟩ := Finset.card_pos.mp hp2
      obtain ⟨hztK, hztt⟩ := (mem_side K x true zt).mp hzt
      have hzf' : zf x ≠ true := by rw [hzff]; decide
      have hzt' : zt x ≠ false := by rw [hztt]; decide
      by_cases hl : (side K x false).card ≤ 2
      · obtain ⟨T', hT'B, hcT', hT'c⟩ := ih (side K x true) (by omega)
          (fun A hA hAc => hm A (hA.trans (side_subset K x true)) hAc)
        obtain ⟨D, hDK, hDc, hDcard⟩ := attach K x hx.1 true zf hzfK hzf' T'
          (hT'B.trans (side_subset K x true)) (fun v hv => hT v (hT'B hv)) hcT'
        exact ⟨D, hDK, hDc, by omega⟩
      by_cases hr : (side K x true).card ≤ 2
      · obtain ⟨T', hT'B, hcT', hT'c⟩ := ih (side K x false) (by omega)
          (fun A hA hAc => hm A (hA.trans (side_subset K x false)) hAc)
        obtain ⟨D, hDK, hDc, hDcard⟩ := attach K x hx.1 false zt hztK hzt' T'
          (hT'B.trans (side_subset K x false)) (fun v hv => hF v (hT'B hv)) hcT'
        exact ⟨D, hDK, hDc, by omega⟩
      have hl3 : 3 ≤ (side K x false).card := by omega
      have hr3 : 3 ≤ (side K x true).card := by omega
      by_cases hcF : Cat (side K x false)
      · obtain ⟨TF, hTFK, hTFc, hTFcard⟩ := attach K x hx.1 false zt hztK hzt'
          (side K x false) (side_subset K x false) hF hcF
        by_cases hcT : Cat (side K x true)
        · obtain ⟨TT, hTTK, hTTc, hTTcard⟩ := attach K x hx.1 true zf hzfK hzf'
            (side K x true) (side_subset K x true) hT hcT
          by_cases hlm : (side K x false).card ≤ (side K x true).card
          · exact ⟨TT, hTTK, hTTc, by omega⟩
          · exact ⟨TF, hTFK, hTFc, by omega⟩
        · have hb := noncat_bound' k t ht3 htk a b hab χ false K (side K x false)
            (side K x true) x hx.1 (side_subset K x false) (side_subset K x true)
            hF hTn hl3 hcT hm
          exact ⟨TF, hTFK, hTFc, by omega⟩
      · by_cases hcT : Cat (side K x true)
        · obtain ⟨TT, hTTK, hTTc, hTTcard⟩ := attach K x hx.1 true zf hzfK hzf'
            (side K x true) (side_subset K x true) hT hcT
          have hb := noncat_bound' k t ht3 htk a b hab χ true K (side K x true)
            (side K x false) x hx.1 (side_subset K x true) (side_subset K x false)
            hT hFn hr3 hcF hm
          exact ⟨TT, hTTK, hTTc, by omega⟩
        · have hb1 := noncat_bound' k t ht3 htk a b hab χ false K (side K x false)
            (side K x true) x hx.1 (side_subset K x false) (side_subset K x true)
            hF hTn hl3 hcT hm
          have hb2 := noncat_bound' k t ht3 htk a b hab χ true K (side K x true)
            (side K x false) x hx.1 (side_subset K x true) (side_subset K x false)
            hT hFn hr3 hcF hm
          obtain ⟨P3, hP3K, hP3c, hP3⟩ := choose_side K x true 3 hr3
          obtain ⟨T4, hT4K, hT4c, hT4card⟩ := attach K x hx.1 true zf hzfK hzf'
            P3 hP3K hP3 (cat_small P3 (by omega))
          exact ⟨T4, hT4K, hT4c, by omega⟩

lemma mono_a {X C : Type*} [LinearOrder X] [Fintype X]
    (k t : ℕ) (ht3 : 3 ≤ t) (htk : 2 * t + 1 ≤ k) (a b : C) (hab : a ≠ b)
    (χ : Finset X → C) (s : ℕ) (hχ : Solon.NoMono χ k s a) :
    Solon.NoMono (colour t a b χ) (k + 1) (max (s + 1) (4 * k - 2 * t - 9)) a := by
  intro K hK
  by_contra hn
  have hm : ∀ A : Finset (X → Bool), A ⊆ K → A.card = k + 1 →
      colour t a b χ A = a := by
    intro A hA hc
    by_contra hne
    exact hn ⟨A, Finset.mem_powersetCard.mpr ⟨hA, hc⟩, hne⟩
  have hK1 : s + 1 ≤ K.card := by
    rw [hK]
    exact le_max_left _ _
  have hK2 : 4 * k - 2 * t - 9 ≤ K.card := by
    rw [hK]
    exact le_max_right _ _
  by_cases hcK : Cat K
  · have := cat_bound k s t a b χ a hχ K hm K (Finset.Subset.refl K) hcK
    omega
  · obtain ⟨T, hTK, hcT, hTc⟩ :=
      extract k t ht3 htk a b hab χ K.card K (le_refl _) hm
    by_cases hTk : k ≤ T.card
    · obtain ⟨A, hAK, hAc, hAnc, hAN⟩ :=
        nc_witness k (by omega) K T hTK hcT hTk hcK
      have h1 := colour_b t a b χ A hAnc (Or.inl hAN)
      exact hab ((hm A hAK hAc).symm.trans h1)
    · omega

lemma mono_other {X C : Type*} [LinearOrder X] [Fintype X]
    (k t : ℕ) (hk : 3 ≤ k) (a b : C) (χ : Finset X → C) (i : C)
    (hia : i ≠ a) (hib : i ≠ b) (s : ℕ) (hs : k ≤ s)
    (hχ : Solon.NoMono χ k s i) :
    Solon.NoMono (colour t a b χ) (k + 1) (s + 1) i := by
  intro K hK
  by_contra hn
  have hm : ∀ A : Finset (X → Bool), A ⊆ K → A.card = k + 1 →
      colour t a b χ A = i := by
    intro A hA hc
    by_contra hne
    exact hn ⟨A, Finset.mem_powersetCard.mpr ⟨hA, hc⟩, hne⟩
  have hcK : Cat K := by
    apply cat_local (k + 1) (by omega) K (by omega)
    intro A hAK hAc
    by_contra hnc
    rcases colour_noncat t a b χ A hnc with h | h
    · exact hia ((hm A hAK hAc).symm.trans h)
    · exact hib ((hm A hAK hAc).symm.trans h)
  have := cat_bound k s t a b χ i hχ K hm K (Finset.Subset.refl K) hcK
  omega

end WinStep

theorem split_window_stepping_up : ∀ {X C : Type*} [LinearOrder X] [Fintype X] [DecidableEq C] (k t : ℕ), 3 ≤ t → 2 * t + 1 ≤ k → ∀ (a b : C), a ≠ b → ∀ (s : C → ℕ), (∀ i, k ≤ s i) → ∀ χ : Finset X → C, (∀ i, Solon.NoMono χ k (s i) i) → ∃ ψ : Finset (X → Bool) → C, Solon.NoMono ψ (k + 1) (max (s a + 1) (4 * k - 2 * t - 9)) a ∧ Solon.NoMono ψ (k + 1) (max (s b + 2) (k + t - 1)) b ∧ ∀ i, i ≠ a → i ≠ b → Solon.NoMono ψ (k + 1) (s i + 1) i := by
  intro X C _ _ _ k t ht3 htk a b hab s hs χ hχ
  exact ⟨WinStep.colour t a b χ,
    WinStep.mono_a k t ht3 htk a b hab χ (s a) (hχ a),
    WinStep.mono_b k t ht3 htk a b hab χ (s b) (hχ b),
    fun i hia hib => WinStep.mono_other k t (by omega) a b χ i hia hib (s i) (hs i) (hχ i)⟩

