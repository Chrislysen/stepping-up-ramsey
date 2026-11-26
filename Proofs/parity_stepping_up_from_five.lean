import Proofs.Defs

set_option maxHeartbeats 0
set_option maxRecDepth 4096

open Classical

namespace EarlyParity

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

lemma bool_cover : ∀ v d e : Bool, d ≠ e → v = d ∨ v = e := by
  intro v d e
  cases v <;> cases d <;> cases e <;> decide

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

lemma card_erase_ge {V : Type*} [DecidableEq V]
    (P : Finset V) (w : V) :
    P.card ≤ (P.erase w).card + 1 := by
  have hsub : P ⊆ insert w (P.erase w) := by
    intro v hv
    by_cases hvw : v = w
    · rw [hvw]
      exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨hvw, hv⟩)
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

lemma cat_local {X : Type*} [LinearOrder X] [Fintype X]
    (m : ℕ) (hm : 4 ≤ m)
    (K : Finset (X → Bool)) (hKm : m ≤ K.card)
    (hall : ∀ A : Finset (X → Bool), A ⊆ K → A.card = m → Cat A) :
    Cat K := by
  intro B hB hBc hbal
  obtain ⟨A, hBA, hAK, hAc⟩ := extend B K m hB (by omega) hKm
  exact hall A hAK hAc B hBA hBc hbal

lemma maximum {X : Type*} [LinearOrder X] [Fintype X]
    (A : Finset (X → Bool)) :
    ∃ T : Finset (X → Bool),
      T ⊆ A ∧ Cat T ∧
      ∀ D : Finset (X → Bool), D ⊆ A → Cat D → D.card ≤ T.card := by
  have hn : (A.powerset.filter (fun T => Cat T)).Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_powerset.mpr (Finset.empty_subset A)
    · exact cat_small ∅ (by simp)
  obtain ⟨T, hT, hmax⟩ :=
    Finset.exists_max_image
      (A.powerset.filter (fun T => Cat T)) Finset.card hn
  obtain ⟨hTA, hcT⟩ := Finset.mem_filter.mp hT
  refine ⟨T, Finset.mem_powerset.mp hTA, hcT, ?_⟩
  intro D hDA hcD
  exact hmax D
    (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hDA, hcD⟩)

noncomputable def maxcat {X : Type*} [LinearOrder X] [Fintype X]
    (A : Finset (X → Bool)) : Finset (X → Bool) :=
  Classical.choose (maximum A)

noncomputable def rank {X : Type*} [LinearOrder X] [Fintype X]
    (A : Finset (X → Bool)) : ℕ :=
  (maxcat A).card

lemma maxcat_spec {X : Type*} [LinearOrder X] [Fintype X]
    (A : Finset (X → Bool)) :
    maxcat A ⊆ A ∧ Cat (maxcat A) ∧
      ∀ D : Finset (X → Bool), D ⊆ A → Cat D → D.card ≤ rank A := by
  exact Classical.choose_spec (maximum A)

lemma rank_max {X : Type*} [LinearOrder X] [Fintype X]
    (D A : Finset (X → Bool)) (hDA : D ⊆ A) (hcD : Cat D) :
    D.card ≤ rank A :=
  (maxcat_spec A).2.2 D hDA hcD

lemma rank_le_card {X : Type*} [LinearOrder X] [Fintype X]
    (A : Finset (X → Bool)) : rank A ≤ A.card :=
  Finset.card_le_card (maxcat_spec A).1

lemma rank_eq_of_cat {X : Type*} [LinearOrder X] [Fintype X]
    (A : Finset (X → Bool)) (hc : Cat A) : rank A = A.card := by
  exact Nat.le_antisymm (rank_le_card A)
    (rank_max A A (Finset.Subset.refl A) hc)

lemma cat_of_rank_eq {X : Type*} [LinearOrder X] [Fintype X]
    (A : Finset (X → Bool)) (h : rank A = A.card) : Cat A := by
  have he : maxcat A = A :=
    Finset.eq_of_subset_of_card_le (maxcat_spec A).1
      (by change A.card ≤ rank A; omega)
  rw [← he]
  exact (maxcat_spec A).2.1

lemma rank_lt_of_notcat {X : Type*} [LinearOrder X] [Fintype X]
    (A : Finset (X → Bool)) (h : ¬ Cat A) : rank A < A.card := by
  have hh := rank_le_card A
  by_contra hn
  exact h (cat_of_rank_eq A (by omega))

lemma rank_mono {X : Type*} [LinearOrder X] [Fintype X]
    {A B : Finset (X → Bool)} (hAB : A ⊆ B) : rank A ≤ rank B :=
  rank_max (maxcat A) B ((maxcat_spec A).1.trans hAB)
    (maxcat_spec A).2.1

def Near {X : Type*} [LinearOrder X] [Fintype X]
    (A : Finset (X → Bool)) : Prop :=
  A.card ≤ rank A + 1

lemma near_sub {X : Type*} [LinearOrder X] [Fintype X]
    {A B : Finset (X → Bool)} (hBA : B ⊆ A) (hA : Near A) :
    Near B := by
  have hI : (maxcat A ∩ B).card ≤ rank B :=
    rank_max (maxcat A ∩ B) B Finset.inter_subset_right
      (cat_sub Finset.inter_subset_left (maxcat_spec A).2.1)
  have hcover : maxcat A ⊆ (maxcat A ∩ B) ∪ (A \ B) := by
    intro v hv
    by_cases hvB : v ∈ B
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hv, hvB⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_sdiff.mpr ⟨(maxcat_spec A).1 hv, hvB⟩)
  have hb := (Finset.card_le_card hcover).trans
    (Finset.card_union_le (maxcat A ∩ B) (A \ B))
  change rank A ≤ (maxcat A ∩ B).card + (A \ B).card at hb
  have hd := Finset.card_sdiff_add_card_eq_card hBA
  unfold Near at hA ⊢
  omega

lemma rank_attach {X : Type*} [LinearOrder X] [Fintype X]
    (z : X → Bool) (A : Finset (X → Bool)) (x : X)
    (hr : ∀ w ∈ A, w x ≠ z x ∧ ∀ y, x < y → w y = z y) :
    rank (insert z A) = rank A + 1 := by
  have hzA : z ∉ A := fun h => (hr z h).1 rfl
  have hzT : z ∉ maxcat A := fun h => hzA ((maxcat_spec A).1 h)
  have hlo := rank_max (insert z (maxcat A)) (insert z A)
    (Finset.insert_subset (Finset.mem_insert_self _ _)
      ((maxcat_spec A).1.trans (Finset.subset_insert z A)))
    (cat_insert z (maxcat A) x
      (fun w hw => hr w ((maxcat_spec A).1 hw))
      (maxcat_spec A).2.1)
  rw [Finset.card_insert_of_notMem hzT] at hlo
  change rank A + 1 ≤ rank (insert z A) at hlo
  have hsub : (maxcat (insert z A)).erase z ⊆ A := by
    intro w hw
    obtain ⟨hwz, hwT⟩ := Finset.mem_erase.mp hw
    exact (Finset.mem_insert.mp ((maxcat_spec (insert z A)).1 hwT)).resolve_left hwz
  have hup := rank_max ((maxcat (insert z A)).erase z) A hsub
    (cat_sub (Finset.erase_subset z _) (maxcat_spec (insert z A)).2.1)
  have he := card_erase_ge (maxcat (insert z A)) z
  change rank (insert z A) ≤
    ((maxcat (insert z A)).erase z).card + 1 at he
  omega

lemma disjoint_bits {X : Type*}
    (x : X) (d e : Bool) (hde : d ≠ e)
    (P Q : Finset (X → Bool))
    (hP : ∀ v ∈ P, v x = d) (hQ : ∀ v ∈ Q, v x = e) :
    Disjoint P Q := by
  rw [Finset.disjoint_left]
  intro v hv hw
  exact hde ((hP v hv).symm.trans (hQ v hw))

lemma cover_bits {X : Type*} [Fintype X]
    (A : Finset (X → Bool)) (x : X) (d e : Bool) (hde : d ≠ e) :
    side A x d ∪ side A x e = A := by
  ext v
  constructor
  · intro hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact ((mem_side A x d v).mp hv).1
    · exact ((mem_side A x e v).mp hv).1
  · intro hv
    rcases bool_cover (v x) d e hde with hd | he
    · exact Finset.mem_union_left _ ((mem_side A x d v).mpr ⟨hv, hd⟩)
    · exact Finset.mem_union_right _ ((mem_side A x e v).mpr ⟨hv, he⟩)

lemma sum_bits {X : Type*} [Fintype X]
    (A : Finset (X → Bool)) (x : X) (d e : Bool) (hde : d ≠ e) :
    (side A x d).card + (side A x e).card = A.card := by
  have hd := disjoint_bits x d e hde (side A x d) (side A x e)
    (fun v hv => ((mem_side A x d v).mp hv).2)
    (fun v hv => ((mem_side A x e v).mp hv).2)
  rw [← Finset.card_union_of_disjoint hd, cover_bits A x d e hde]

lemma side_join {X : Type*} [Fintype X]
    (x : X) (d e : Bool) (hde : d ≠ e)
    (P Q : Finset (X → Bool))
    (hP : ∀ v ∈ P, v x = d) (hQ : ∀ v ∈ Q, v x = e) :
    side (P ∪ Q) x d = P ∧ side (P ∪ Q) x e = Q := by
  constructor
  · ext v
    constructor
    · intro hv
      obtain ⟨hv, hb⟩ := (mem_side (P ∪ Q) x d v).mp hv
      rcases Finset.mem_union.mp hv with hp | hq
      · exact hp
      · exact (hde (hb.symm.trans (hQ v hq))).elim
    · intro hv
      exact (mem_side (P ∪ Q) x d v).mpr
        ⟨Finset.mem_union_left _ hv, hP v hv⟩
  · ext v
    constructor
    · intro hv
      obtain ⟨hv, hb⟩ := (mem_side (P ∪ Q) x e v).mp hv
      rcases Finset.mem_union.mp hv with hp | hq
      · exact (hde ((hP v hp).symm.trans hb)).elim
      · exact hq
    · intro hv
      exact (mem_side (P ∪ Q) x e v).mpr
        ⟨Finset.mem_union_right _ hv, hQ v hv⟩

lemma cat_split_bits {X : Type*} [LinearOrder X] [Fintype X]
    (A : Finset (X → Bool)) (x : X) (d e : Bool) (hde : d ≠ e)
    (hc : Cat A) (hag : Above A x) :
    (side A x d).card ≤ 1 ∨ (side A x e).card ≤ 1 := by
  cases d <;> cases e
  · exact (hde rfl).elim
  · exact cat_split hc hag
  · exact (cat_split hc hag).symm
  · exact (hde rfl).elim

lemma rank_split_bound {X : Type*} [LinearOrder X] [Fintype X]
    (A : Finset (X → Bool)) (x : X) (d e : Bool) (hde : d ≠ e)
    (hag : Above A x) :
    rank A ≤ max (rank (side A x d)) (rank (side A x e)) + 1 := by
  have hc := (maxcat_spec A).2.1
  have hsub := (maxcat_spec A).1
  have hs := cat_split_bits (maxcat A) x d e hde hc (above_sub hsub hag)
  have hsum := sum_bits (maxcat A) x d e hde
  change (side (maxcat A) x d).card +
    (side (maxcat A) x e).card = rank A at hsum
  have hd : (side (maxcat A) x d).card ≤ rank (side A x d) := by
    apply rank_max
    · intro v hv
      obtain ⟨hvT, hvd⟩ := (mem_side (maxcat A) x d v).mp hv
      exact (mem_side A x d v).mpr ⟨hsub hvT, hvd⟩
    · exact cat_sub (side_subset (maxcat A) x d) hc
  have he : (side (maxcat A) x e).card ≤ rank (side A x e) := by
    apply rank_max
    · intro v hv
      obtain ⟨hvT, hve⟩ := (mem_side (maxcat A) x e v).mp hv
      exact (mem_side A x e v).mpr ⟨hsub hvT, hve⟩
    · exact cat_sub (side_subset (maxcat A) x e) hc
  have hm1 := le_max_left (rank (side A x d)) (rank (side A x e))
  have hm2 := le_max_right (rank (side A x d)) (rank (side A x e))
  omega

lemma join_rank {X : Type*} [LinearOrder X] [Fintype X]
    (x : X) (d e : Bool) (hde : d ≠ e)
    (P Q : Finset (X → Bool))
    (hag : Above (P ∪ Q) x)
    (hP : ∀ v ∈ P, v x = d) (hQ : ∀ v ∈ Q, v x = e)
    (hPn : 0 < P.card) (hQn : 0 < Q.card) :
    rank (P ∪ Q) = max (rank P) (rank Q) + 1 := by
  have hup := rank_split_bound (P ∪ Q) x d e hde hag
  obtain ⟨hd, he⟩ := side_join x d e hde P Q hP hQ
  rw [hd, he] at hup
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hPn
  obtain ⟨q, hq⟩ := Finset.card_pos.mp hQn
  have hrP : ∀ w ∈ P, w x ≠ q x ∧ ∀ y, x < y → w y = q y := by
    intro w hw
    refine ⟨?_, fun y hy =>
      hag w (Finset.mem_union_left _ hw) q (Finset.mem_union_right _ hq) y hy⟩
    intro hh
    exact hde ((hP w hw).symm.trans (hh.trans (hQ q hq)))
  have hrQ : ∀ w ∈ Q, w x ≠ p x ∧ ∀ y, x < y → w y = p y := by
    intro w hw
    refine ⟨?_, fun y hy =>
      hag w (Finset.mem_union_right _ hw) p (Finset.mem_union_left _ hp) y hy⟩
    intro hh
    exact hde ((hP p hp).symm.trans (hh.symm.trans (hQ w hw)))
  have hlP := rank_mono
    (Finset.insert_subset (Finset.mem_union_right P hq)
      (Finset.subset_union_left : P ⊆ P ∪ Q))
  rw [rank_attach q P x hrP] at hlP
  have hlQ := rank_mono
    (Finset.insert_subset (Finset.mem_union_left Q hp)
      (Finset.subset_union_right : Q ⊆ P ∪ Q))
  rw [rank_attach p Q x hrQ] at hlQ
  omega

lemma split_rank {X : Type*} [LinearOrder X] [Fintype X]
    (K : Finset (X → Bool)) (x : X) (d e : Bool) (hde : d ≠ e)
    (hag : Above K x)
    (hd : 0 < (side K x d).card) (he : 0 < (side K x e).card) :
    rank K = max (rank (side K x d)) (rank (side K x e)) + 1 := by
  have hu := cover_bits K x d e hde
  have hh := join_rank x d e hde (side K x d) (side K x e)
    (above_sub (Finset.union_subset (side_subset K x d) (side_subset K x e)) hag)
    (fun v hv => ((mem_side K x d v).mp hv).2)
    (fun v hv => ((mem_side K x e v).mp hv).2) hd he
  rwa [hu] at hh

lemma near_local {X : Type*} [LinearOrder X] [Fintype X] :
    ∀ n : ℕ, ∀ K : Finset (X → Bool), K.card ≤ n →
      (∀ U : Finset (X → Bool), U ⊆ K → U.card ≤ 6 → Near U) →
      Near K := by
  intro n
  induction n with
  | zero =>
      intro K hK hall
      exact hall K (Finset.Subset.refl K) (by omega)
  | succ n ih =>
      intro K hKn hall
      by_cases hsmall : K.card ≤ 6
      · exact hall K (Finset.Subset.refl K) hsmall
      obtain ⟨x, hx⟩ := top K (by omega)
      obtain ⟨hf, ht⟩ := split_pos hx
      have go (d e : Bool) (hde : d ≠ e)
          (hd : 0 < (side K x d).card) (he : 0 < (side K x e).card)
          (hsmallD : (side K x d).card ≤ 2) : Near K := by
        have hsum := sum_bits K x d e hde
        have hrank := split_rank K x d e hde hx.1 hd he
        have hm := le_max_right (rank (side K x d)) (rank (side K x e))
        have hEN := ih (side K x e) (by omega)
          (fun U hU hUc => hall U (hU.trans (side_subset K x e)) hUc)
        by_cases hd1 : (side K x d).card = 1
        · unfold Near at hEN ⊢
          omega
        have hd2 : (side K x d).card = 2 := by omega
        have hcE : Cat (side K x e) := by
          by_contra hn
          obtain ⟨W, hWE, hWc, hWb⟩ := bad_four (side K x e) hn
          have hnW : ¬ Cat W := fun hc =>
            hc W (Finset.Subset.refl W) hWc hWb
          have hWr := rank_lt_of_notcat W hnW
          have hDr := rank_le_card (side K x d)
          have hDbit : ∀ v ∈ side K x d, v x = d :=
            fun v hv => ((mem_side K x d v).mp hv).2
          have hWbit : ∀ v ∈ W, v x = e :=
            fun v hv => ((mem_side K x e v).mp (hWE hv)).2
          have hUK : side K x d ∪ W ⊆ K :=
            Finset.union_subset (side_subset K x d)
              (hWE.trans (side_subset K x e))
          have hUc : (side K x d ∪ W).card = 6 := by
            rw [Finset.card_union_of_disjoint
              (disjoint_bits x d e hde _ _ hDbit hWbit), hd2, hWc]
          have hUr := join_rank x d e hde (side K x d) W
            (above_sub hUK hx.1) hDbit hWbit (by omega) (by omega)
          have hmax : max (rank (side K x d)) (rank W) ≤ 3 :=
            max_le (by omega) (by omega)
          have hUN := hall (side K x d ∪ W) hUK (by omega)
          unfold Near at hUN
          omega
        have hEr := rank_eq_of_cat (side K x e) hcE
        unfold Near
        omega
      by_cases hf2 : (side K x false).card ≤ 2
      · exact go false true ft hf ht hf2
      by_cases ht2 : (side K x true).card ≤ 2
      · exact go true false ft.symm ht hf ht2
      obtain ⟨P, hPK, hPc, hP⟩ := choose_side K x false 3 (by omega)
      obtain ⟨Q, hQK, hQc, hQ⟩ := choose_side K x true 3 (by omega)
      have hUK : P ∪ Q ⊆ K := Finset.union_subset hPK hQK
      have hUc : (P ∪ Q).card = 6 := by
        rw [Finset.card_union_of_disjoint (bits_disjoint x P Q hP hQ), hPc, hQc]
      have hUr := join_rank x false true ft P Q (above_sub hUK hx.1)
        hP hQ (by omega) (by omega)
      have hPr := rank_le_card P
      have hQr := rank_le_card Q
      have hmax : max (rank P) (rank Q) ≤ 3 := max_le (by omega) (by omega)
      have hUN := hall (P ∪ Q) hUK (by omega)
      unfold Near at hUN
      omega

noncomputable def paint {X : Type*} [LinearOrder X] [Fintype X]
    (χ : Finset X → Fin 2) (A : Finset (X → Bool)) : Fin 2 :=
  if Cat A then χ (levels A)
  else if (A.card - rank A) % 2 = 0 then 0 else 1

lemma paint_cat {X : Type*} [LinearOrder X] [Fintype X]
    (χ : Finset X → Fin 2) (A : Finset (X → Bool)) (hc : Cat A) :
    paint χ A = χ (levels A) := by
  unfold paint
  rw [if_pos hc]

lemma paint_zero {X : Type*} [LinearOrder X] [Fintype X]
    (χ : Finset X → Fin 2) (A : Finset (X → Bool))
    (hn : ¬ Cat A) (he : (A.card - rank A) % 2 = 0) :
    paint χ A = 0 := by
  unfold paint
  rw [if_neg hn, if_pos he]

lemma paint_one {X : Type*} [LinearOrder X] [Fintype X]
    (χ : Finset X → Fin 2) (A : Finset (X → Bool))
    (hn : ¬ Cat A) (he : (A.card - rank A) % 2 ≠ 0) :
    paint χ A = 1 := by
  unfold paint
  rw [if_neg hn, if_neg he]

lemma cat_bound {X : Type*} [LinearOrder X] [Fintype X]
    (k s : ℕ) (χ : Finset X → Fin 2) (i : Fin 2)
    (hχ : Solon.NoMono χ k s i)
    (K : Finset (X → Bool))
    (hm : ∀ A : Finset (X → Bool),
      A ⊆ K → A.card = k + 1 → paint χ A = i)
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
  rw [paint_cat χ A (cat_sub hAD hc), hAt] at hcol
  exact hne hcol

lemma exchange {X : Type*} [LinearOrder X] [Fintype X]
    (k : ℕ) (K : Finset (X → Bool)) (x : X)
    (d e : Bool) (hde : d ≠ e) (hag : Above K x)
    (A : Finset (X → Bool)) (hAL : A ⊆ side K x d)
    (hAc : A.card = k + 1) (hnc : ¬ Cat A)
    (r : X → Bool) (hrK : r ∈ K) (hre : r x = e) :
    ∃ B : Finset (X → Bool),
      B ⊆ K ∧ B.card = k + 1 ∧ rank B = rank A + 1 := by
  have hex : ∃ p ∈ A, p ∉ maxcat A := by
    by_contra hn
    have hAM : A ⊆ maxcat A := by
      intro p hp
      by_contra hpM
      exact hn ⟨p, hp, hpM⟩
    exact hnc (cat_sub hAM (maxcat_spec A).2.1)
  obtain ⟨p, hpA, hpM⟩ := hex
  have hME : maxcat A ⊆ A.erase p := by
    intro v hv
    refine Finset.mem_erase.mpr ⟨?_, (maxcat_spec A).1 hv⟩
    intro hvp
    exact hpM (hvp ▸ hv)
  have hlow := rank_max (maxcat A) (A.erase p) hME (maxcat_spec A).2.1
  change rank A ≤ rank (A.erase p) at hlow
  have hupp := rank_mono (Finset.erase_subset p A)
  have hEr : rank (A.erase p) = rank A := by omega
  have hAK : A ⊆ K := hAL.trans (side_subset K x d)
  have hrel : ∀ w ∈ A.erase p,
      w x ≠ r x ∧ ∀ y, x < y → w y = r y := by
    intro w hw
    have hwA := Finset.mem_of_mem_erase hw
    have hwd := ((mem_side K x d w).mp (hAL hwA)).2
    refine ⟨?_, fun y hy => hag w (hAK hwA) r hrK y hy⟩
    intro hh
    exact hde (hwd.symm.trans (hh.trans hre))
  have hrE : r ∉ A.erase p := fun h => (hrel r h).1 rfl
  refine ⟨insert r (A.erase p),
    Finset.insert_subset hrK ((Finset.erase_subset p A).trans hAK), ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem hrE, Finset.card_erase_of_mem hpA, hAc]
    omega
  · rw [rank_attach r (A.erase p) x hrel, hEr]

lemma red_side_cat {X : Type*} [LinearOrder X] [Fintype X]
    (k : ℕ) (hk : 5 ≤ k) (χ : Finset X → Fin 2)
    (K : Finset (X → Bool)) (x : X) (d e : Bool) (hde : d ≠ e)
    (hag : Above K x)
    (hL : k + 1 ≤ (side K x d).card)
    (hR : 0 < (side K x e).card)
    (hm : ∀ A : Finset (X → Bool),
      A ⊆ K → A.card = k + 1 → paint χ A = 0) :
    Cat (side K x d) := by
  apply cat_local (k + 1) (by omega) (side K x d) hL
  intro A hAL hAc
  by_contra hn
  have hAr := rank_lt_of_notcat A hn
  have hAK : A ⊆ K := hAL.trans (side_subset K x d)
  by_cases heven : (A.card - rank A) % 2 = 0
  · have hgap : rank A + 2 ≤ A.card := by omega
    obtain ⟨r, hr⟩ := Finset.card_pos.mp hR
    obtain ⟨hrK, hre⟩ := (mem_side K x e r).mp hr
    obtain ⟨B, hBK, hBc, hBr⟩ :=
      exchange k K x d e hde hag A hAL hAc hn r hrK hre
    have hBn : ¬ Cat B := by
      intro hc
      have hh := rank_eq_of_cat B hc
      omega
    have hodd : (B.card - rank B) % 2 ≠ 0 := by omega
    have hh : (0 : Fin 2) = 1 :=
      (hm B hBK hBc).symm.trans (paint_one χ B hBn hodd)
    exact (by decide : (0 : Fin 2) ≠ 1) hh
  · have hh : (0 : Fin 2) = 1 :=
      (hm A hAK hAc).symm.trans (paint_one χ A hn heven)
    exact (by decide : (0 : Fin 2) ≠ 1) hh

lemma blue_side_near {X : Type*} [LinearOrder X] [Fintype X]
    (k : ℕ) (hk : 5 ≤ k) (χ : Finset X → Fin 2)
    (K : Finset (X → Bool)) (x : X) (d e : Bool) (hde : d ≠ e)
    (hag : Above K x)
    (hL : k + 1 ≤ (side K x d).card)
    (hR : 0 < (side K x e).card)
    (hm : ∀ A : Finset (X → Bool),
      A ⊆ K → A.card = k + 1 → paint χ A = 1) :
    Near (side K x d) := by
  apply near_local (side K x d).card (side K x d) (le_refl _)
  intro U hUL hUc
  obtain ⟨A, hUA, hAL, hAc⟩ :=
    extend U (side K x d) (k + 1) hUL (by omega) hL
  have hAN : Near A := by
    by_contra hn
    have hgap : rank A + 2 ≤ A.card := by
      unfold Near at hn
      omega
    have hnc : ¬ Cat A := by
      intro hc
      have hh := rank_eq_of_cat A hc
      omega
    have hAK : A ⊆ K := hAL.trans (side_subset K x d)
    by_cases heven : (A.card - rank A) % 2 = 0
    · have hh : (1 : Fin 2) = 0 :=
        (hm A hAK hAc).symm.trans (paint_zero χ A hnc heven)
      exact (by decide : (1 : Fin 2) ≠ 0) hh
    · obtain ⟨r, hr⟩ := Finset.card_pos.mp hR
      obtain ⟨hrK, hre⟩ := (mem_side K x e r).mp hr
      obtain ⟨B, hBK, hBc, hBr⟩ :=
        exchange k K x d e hde hag A hAL hAc hnc r hrK hre
      have hBn : ¬ Cat B := by
        intro hc
        have hh := rank_eq_of_cat B hc
        omega
      have hBeven : (B.card - rank B) % 2 = 0 := by omega
      have hh : (1 : Fin 2) = 0 :=
        (hm B hBK hBc).symm.trans (paint_zero χ B hBn hBeven)
      exact (by decide : (1 : Fin 2) ≠ 0) hh
  exact near_sub hUA hAN

lemma forbid_one {X : Type*} [LinearOrder X] [Fintype X]
    (k : ℕ) (χ : Finset X → Fin 2) (K A : Finset (X → Bool))
    (hm : ∀ B : Finset (X → Bool),
      B ⊆ K → B.card = k + 1 → paint χ B = 0)
    (hAK : A ⊆ K) (hAc : A.card = k + 1)
    (hgap : rank A + 1 = A.card) : False := by
  have hn : ¬ Cat A := by
    intro hc
    have hh := rank_eq_of_cat A hc
    omega
  have hodd : (A.card - rank A) % 2 ≠ 0 := by omega
  have hh : (0 : Fin 2) = 1 :=
    (hm A hAK hAc).symm.trans (paint_one χ A hn hodd)
  exact (by decide : (0 : Fin 2) ≠ 1) hh

lemma forbid_two {X : Type*} [LinearOrder X] [Fintype X]
    (k : ℕ) (χ : Finset X → Fin 2) (K A : Finset (X → Bool))
    (hm : ∀ B : Finset (X → Bool),
      B ⊆ K → B.card = k + 1 → paint χ B = 1)
    (hAK : A ⊆ K) (hAc : A.card = k + 1)
    (hgap : rank A + 2 = A.card) : False := by
  have hn : ¬ Cat A := by
    intro hc
    have hh := rank_eq_of_cat A hc
    omega
  have heven : (A.card - rank A) % 2 = 0 := by omega
  have hh : (1 : Fin 2) = 0 :=
    (hm A hAK hAc).symm.trans (paint_zero χ A hn heven)
  exact (by decide : (1 : Fin 2) ≠ 0) hh

lemma large_red {X : Type*} [LinearOrder X] [Fintype X]
    (k : ℕ) (hk : 5 ≤ k) (χ : Finset X → Fin 2)
    (K : Finset (X → Bool)) (x : X) (d e : Bool) (hde : d ≠ e)
    (hag : Above K x)
    (hL : k + 1 ≤ (side K x d).card)
    (hR : 0 < (side K x e).card)
    (hm : ∀ A : Finset (X → Bool),
      A ⊆ K → A.card = k + 1 → paint χ A = 0) :
    Cat K := by
  have hcL := red_side_cat k hk χ K x d e hde hag hL hR hm
  have hRsmall : (side K x e).card ≤ 1 := by
    by_contra hn
    obtain ⟨P, hPL, hPc⟩ :=
      Finset.exists_subset_card_eq
        (show k - 1 ≤ (side K x d).card by omega)
    obtain ⟨Q, hQR, hQc⟩ :=
      Finset.exists_subset_card_eq
        (show 2 ≤ (side K x e).card by omega)
    have hP : ∀ v ∈ P, v x = d :=
      fun v hv => ((mem_side K x d v).mp (hPL hv)).2
    have hQ : ∀ v ∈ Q, v x = e :=
      fun v hv => ((mem_side K x e v).mp (hQR hv)).2
    have hUK : P ∪ Q ⊆ K :=
      Finset.union_subset
        (hPL.trans (side_subset K x d)) (hQR.trans (side_subset K x e))
    have hUc : (P ∪ Q).card = k + 1 := by
      rw [Finset.card_union_of_disjoint (disjoint_bits x d e hde P Q hP hQ),
        hPc, hQc]
      omega
    have hPr := rank_eq_of_cat P (cat_sub hPL hcL)
    have hQr := rank_eq_of_cat Q (cat_small Q (by omega))
    have hUr := join_rank x d e hde P Q (above_sub hUK hag)
      hP hQ (by omega) (by omega)
    exact forbid_one k χ K (P ∪ Q) hm hUK hUc (by omega)
  have hsum := sum_bits K x d e hde
  have hLr := rank_eq_of_cat (side K x d) hcL
  have hRr := rank_eq_of_cat (side K x e)
    (cat_small (side K x e) (by omega))
  have hKr := split_rank K x d e hde hag (by omega) hR
  apply cat_of_rank_eq K
  omega

lemma large_blue {X : Type*} [LinearOrder X] [Fintype X]
    (k : ℕ) (hk : 5 ≤ k) (χ : Finset X → Fin 2)
    (K : Finset (X → Bool)) (x : X) (d e : Bool) (hde : d ≠ e)
    (hag : Above K x)
    (hL : k + 1 ≤ (side K x d).card)
    (hR : 0 < (side K x e).card)
    (hm : ∀ A : Finset (X → Bool),
      A ⊆ K → A.card = k + 1 → paint χ A = 1) :
    Near K := by
  have hLN := blue_side_near k hk χ K x d e hde hag hL hR hm
  have hLrank : k ≤ rank (side K x d) := by
    unfold Near at hLN
    omega
  have hRsmall : (side K x e).card ≤ 2 := by
    by_contra hn
    obtain ⟨P, hPT, hPc⟩ :=
      Finset.exists_subset_card_eq
        (show k - 2 ≤ (maxcat (side K x d)).card by
          change k - 2 ≤ rank (side K x d)
          omega)
    have hPL : P ⊆ side K x d :=
      hPT.trans (maxcat_spec (side K x d)).1
    have hcP : Cat P :=
      cat_sub hPT (maxcat_spec (side K x d)).2.1
    obtain ⟨Q, hQR, hQc⟩ :=
      Finset.exists_subset_card_eq
        (show 3 ≤ (side K x e).card by omega)
    have hcQ : Cat Q := cat_small Q (by omega)
    have hP : ∀ v ∈ P, v x = d :=
      fun v hv => ((mem_side K x d v).mp (hPL hv)).2
    have hQ : ∀ v ∈ Q, v x = e :=
      fun v hv => ((mem_side K x e v).mp (hQR hv)).2
    have hUK : P ∪ Q ⊆ K :=
      Finset.union_subset
        (hPL.trans (side_subset K x d)) (hQR.trans (side_subset K x e))
    have hUc : (P ∪ Q).card = k + 1 := by
      rw [Finset.card_union_of_disjoint (disjoint_bits x d e hde P Q hP hQ),
        hPc, hQc]
      omega
    have hPr := rank_eq_of_cat P hcP
    have hQr := rank_eq_of_cat Q hcQ
    have hUr := join_rank x d e hde P Q (above_sub hUK hag)
      hP hQ (by omega) (by omega)
    exact forbid_two k χ K (P ∪ Q) hm hUK hUc (by omega)
  have hsum := sum_bits K x d e hde
  have hKr := split_rank K x d e hde hag (by omega) hR
  have hmax := le_max_left (rank (side K x d)) (rank (side K x e))
  by_cases hR2 : (side K x e).card = 2
  · have hcL : Cat (side K x d) := by
      by_contra hn
      obtain ⟨W, hWL, hWc, hWb⟩ := bad_four (side K x d) hn
      obtain ⟨P, hWP, hPL, hPc⟩ :=
        extend W (side K x d) (k - 1) hWL (by omega) (by omega)
      have hPn : ¬ Cat P := fun hc => hc W hWP hWc hWb
      have hPN := near_sub hPL hLN
      have hPrlt := rank_lt_of_notcat P hPn
      have hPr : rank P = k - 2 := by
        unfold Near at hPN
        omega
      have hQr := rank_eq_of_cat (side K x e)
        (cat_small (side K x e) (by omega))
      have hP : ∀ v ∈ P, v x = d :=
        fun v hv => ((mem_side K x d v).mp (hPL hv)).2
      have hQ : ∀ v ∈ side K x e, v x = e :=
        fun v hv => ((mem_side K x e v).mp hv).2
      have hUK : P ∪ side K x e ⊆ K :=
        Finset.union_subset (hPL.trans (side_subset K x d))
          (side_subset K x e)
      have hUc : (P ∪ side K x e).card = k + 1 := by
        rw [Finset.card_union_of_disjoint
          (disjoint_bits x d e hde P (side K x e) hP hQ), hPc, hR2]
        omega
      have hUr := join_rank x d e hde P (side K x e)
        (above_sub hUK hag) hP hQ (by omega) hR
      exact forbid_two k χ K (P ∪ side K x e) hm hUK hUc (by omega)
    have hLr := rank_eq_of_cat (side K x d) hcL
    unfold Near
    omega
  · have hR1 : (side K x e).card = 1 := by omega
    unfold Near at hLN ⊢
    omega

end EarlyParity

theorem parity_stepping_up_from_five :
    ∀ {X : Type*} [LinearOrder X] [Fintype X] (k s t : ℕ),
      5 ≤ k →
      k + 1 ≤ s →
      k + 1 ≤ t →
      ∀ χ : Finset X → Fin 2,
        Solon.NoMono χ k s 0 →
        Solon.NoMono χ k t 1 →
        ∃ ψ : Finset (X → Bool) → Fin 2,
          Solon.NoMono ψ (k + 1) (earlyParitySize k s 1) 0 ∧
          Solon.NoMono ψ (k + 1) (earlyParitySize k t 2) 1 := by
  intro X _ _ k s t hk _ _ χ hχ0 hχ1
  classical
  refine ⟨EarlyParity.paint χ, ?_, ?_⟩
  · intro K hK
    change K.card = max (s + 1) (2 * k + 1) at hK
    by_contra hn
    have hm : ∀ A : Finset (X → Bool),
        A ⊆ K → A.card = k + 1 → EarlyParity.paint χ A = 0 := by
      intro A hAK hAc
      by_contra hne
      exact hn ⟨A, Finset.mem_powersetCard.mpr ⟨hAK, hAc⟩, hne⟩
    have hbig : 2 * k + 1 ≤ K.card := by
      rw [hK]
      exact le_max_right _ _
    have htarget : s + 1 ≤ K.card := by
      rw [hK]
      exact le_max_left _ _
    obtain ⟨x, hx⟩ := EarlyParity.top K (by omega)
    obtain ⟨hf, ht⟩ := EarlyParity.split_pos hx
    have hsum := EarlyParity.side_card_sum K x
    have hcK : EarlyParity.Cat K := by
      by_cases hL : k + 1 ≤ (EarlyParity.side K x false).card
      · exact EarlyParity.large_red k hk χ K x false true
          EarlyParity.ft hx.1 hL ht hm
      · exact EarlyParity.large_red k hk χ K x true false
          EarlyParity.ft.symm hx.1 (by omega) hf hm
    have hb := EarlyParity.cat_bound k s χ 0 hχ0 K hm K
      (Finset.Subset.refl K) hcK
    omega
  · intro K hK
    change K.card = max (t + 2) (2 * k + 1) at hK
    by_contra hn
    have hm : ∀ A : Finset (X → Bool),
        A ⊆ K → A.card = k + 1 → EarlyParity.paint χ A = 1 := by
      intro A hAK hAc
      by_contra hne
      exact hn ⟨A, Finset.mem_powersetCard.mpr ⟨hAK, hAc⟩, hne⟩
    have hbig : 2 * k + 1 ≤ K.card := by
      rw [hK]
      exact le_max_right _ _
    have htarget : t + 2 ≤ K.card := by
      rw [hK]
      exact le_max_left _ _
    obtain ⟨x, hx⟩ := EarlyParity.top K (by omega)
    obtain ⟨hf, ht⟩ := EarlyParity.split_pos hx
    have hsum := EarlyParity.side_card_sum K x
    have hNK : EarlyParity.Near K := by
      by_cases hL : k + 1 ≤ (EarlyParity.side K x false).card
      · exact EarlyParity.large_blue k hk χ K x false true
          EarlyParity.ft hx.1 hL ht hm
      · exact EarlyParity.large_blue k hk χ K x true false
          EarlyParity.ft.symm hx.1 (by omega) hf hm
    have hb := EarlyParity.cat_bound k t χ 1 hχ1 K hm
      (EarlyParity.maxcat K) (EarlyParity.maxcat_spec K).1
      (EarlyParity.maxcat_spec K).2.1
    change EarlyParity.rank K ≤ t at hb
    unfold EarlyParity.Near at hNK
    omega

