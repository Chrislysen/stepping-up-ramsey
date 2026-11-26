import Proofs.Defs

set_option maxHeartbeats 0
set_option maxRecDepth 4096

open Classical

namespace OddStep

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

lemma not_ne (d : Bool) : (!d) ≠ d := by cases d <;> decide

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

lemma attach_side {X : Type*} [LinearOrder X] [Fintype X]
    (K : Finset (X → Bool)) (x : X) (hag : Above K x)
    (d : Bool) (z : X → Bool) (hz : z ∈ K) (hzd : z x ≠ d)
    (T : Finset (X → Bool)) (hT : T ⊆ side K x d) (hc : Cat T) :
    ∃ D : Finset (X → Bool), D ⊆ K ∧ Cat D ∧ D.card = T.card + 1 := by
  have hTK : T ⊆ K := hT.trans (side_subset K x d)
  have hzT : z ∉ T := fun h => hzd ((mem_side K x d z).mp (hT h)).2
  have hr : ∀ w ∈ T, w x ≠ z x ∧ ∀ y, x < y → w y = z y := by
    intro w hw
    have hwd := ((mem_side K x d w).mp (hT hw)).2
    refine ⟨?_, fun y hy => hag w (hTK hw) z hz y hy⟩
    intro he
    exact hzd (he.symm.trans hwd)
  exact ⟨insert z T, Finset.insert_subset hz hTK, cat_insert z T x hr hc,
    Finset.card_insert_of_notMem hzT⟩

lemma cat_local {X : Type*} [LinearOrder X] [Fintype X] (m : ℕ) (hm : 4 ≤ m)
    (K : Finset (X → Bool)) (hKm : m ≤ K.card)
    (hall : ∀ A : Finset (X → Bool), A ⊆ K → A.card = m → Cat A) : Cat K := by
  intro B hB hBc hbal
  obtain ⟨A, hBA, hAK, hAc⟩ := extend B K m hB (by omega) hKm
  exact hall A hAK hAc B hBA hBc hbal

def OddSplit {X : Type*} [LinearOrder X]
    (A : Finset (X → Bool)) : Prop :=
  ∃ x : X, Split A x ∧ 3 ≤ (side A x false).card ∧
    3 ≤ (side A x true).card ∧
    (side A x false).card % 2 = 1 ∧ (side A x true).card % 2 = 1

noncomputable def colour {X C : Type*} [LinearOrder X] [Fintype X]
    (a b : C) (χ : Finset X → C) (A : Finset (X → Bool)) : C :=
  if Cat A then χ (levels A)
  else if OddSplit A then a else b

lemma colour_cat {X C : Type*} [LinearOrder X] [Fintype X]
    (a b : C) (χ : Finset X → C) (A : Finset (X → Bool)) (hc : Cat A) :
    colour a b χ A = χ (levels A) := by
  unfold colour
  rw [if_pos hc]

lemma colour_a {X C : Type*} [LinearOrder X] [Fintype X]
    (a b : C) (χ : Finset X → C) (A : Finset (X → Bool)) (hc : ¬ Cat A)
    (h : OddSplit A) : colour a b χ A = a := by
  unfold colour
  rw [if_neg hc, if_pos h]

lemma colour_b {X C : Type*} [LinearOrder X] [Fintype X]
    (a b : C) (χ : Finset X → C) (A : Finset (X → Bool)) (hc : ¬ Cat A)
    (h : ¬ OddSplit A) : colour a b χ A = b := by
  unfold colour
  rw [if_neg hc, if_neg h]

lemma colour_noncat {X C : Type*} [LinearOrder X] [Fintype X]
    (a b : C) (χ : Finset X → C) (A : Finset (X → Bool)) (hc : ¬ Cat A) :
    colour a b χ A = a ∨ colour a b χ A = b := by
  by_cases h : OddSplit A
  · exact Or.inl (colour_a a b χ A hc h)
  · exact Or.inr (colour_b a b χ A hc h)

lemma noncat_sides {X : Type*} [LinearOrder X] [Fintype X]
    {A : Finset (X → Bool)} {x : X} (hag : Above A x)
    (hf : 2 ≤ (side A x false).card) (ht : 2 ≤ (side A x true).card) :
    ¬ Cat A := by
  intro hc
  have := cat_split hc hag
  omega

lemma colour_b_two {X C : Type*} [LinearOrder X] [Fintype X]
    (a b : C) (χ : Finset X → C) (A : Finset (X → Bool)) (x : X)
    (hag : Above A x)
    (hf : 2 ≤ (side A x false).card) (ht : 2 ≤ (side A x true).card)
    (hp : (side A x false).card % 2 = 0 ∨ (side A x true).card % 2 = 0) :
    colour a b χ A = b := by
  apply colour_b a b χ A (noncat_sides hag hf ht)
  rintro ⟨y, hy, h1, h2, h3, h4⟩
  have hx : Split A x := split_of_pos hag (by omega) (by omega)
  have hyx : y = x := split_unique hy hx
  subst hyx
  omega

lemma colour_b_gen {X C : Type*} [LinearOrder X] [Fintype X]
    (a b : C) (χ : Finset X → C) (d : Bool) (A : Finset (X → Bool)) (x : X)
    (hag : Above A x)
    (h1 : 2 ≤ (side A x d).card) (h2 : 2 ≤ (side A x (!d)).card)
    (hp : (side A x d).card % 2 = 0) :
    colour a b χ A = b := by
  cases d
  · exact colour_b_two a b χ A x hag h1 h2 (Or.inl hp)
  · exact colour_b_two a b χ A x hag h2 h1 (Or.inr hp)

lemma not_odd_small {X : Type*} [LinearOrder X] [Fintype X]
    (d : Bool) {A : Finset (X → Bool)} {x : X} (hx : Split A x)
    (hd : (side A x d).card < 3) : ¬ OddSplit A := by
  rintro ⟨y, hy, h1, h2, _, _⟩
  have hyx : y = x := split_unique hy hx
  subst hyx
  cases d <;> omega

lemma side_erase {X : Type*} [Fintype X] (A : Finset (X → Bool)) (x : X) (c : Bool)
    (w : X → Bool) : side (A.erase w) x c = (side A x c).erase w := by
  ext v
  simp only [side, Finset.mem_filter, Finset.mem_erase]
  tauto

lemma erase_not {V : Type*} [DecidableEq V] (S : Finset V) (w : V)
    (h : w ∉ S) : S.erase w = S := by
  ext v
  rw [Finset.mem_erase]
  constructor
  · intro hv
    exact hv.2
  · intro hv
    exact ⟨fun e => h (by rw [← e]; exact hv), hv⟩

lemma even_case {X C : Type*} [LinearOrder X] [Fintype X]
    (k : ℕ) (a b : C) (hab : a ≠ b) (χ : Finset X → C)
    (K : Finset (X → Bool)) (x : X) (d : Bool) (hag : Above K x)
    (hKc : K.card = k + 2)
    (ho : 3 ≤ (side K x d).card) (hpar : (side K x d).card % 2 = 1)
    (he : 2 ≤ (side K x (!d)).card)
    (hm : ∀ A : Finset (X → Bool), A ⊆ K → A.card = k + 1 →
      colour a b χ A = a) : False := by
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (show 0 < (side K x d).card by omega)
  obtain ⟨hwK, hwx⟩ := (mem_side K x d w).mp hw
  have hA1 : side (K.erase w) x d = (side K x d).erase w := side_erase K x d w
  have hA2 : side (K.erase w) x (!d) = side K x (!d) := by
    rw [side_erase]
    apply erase_not
    intro hw'
    have hh := ((mem_side K x (!d) w).mp hw').2
    rw [hwx] at hh
    exact not_ne d hh.symm
  have hc1 : (side (K.erase w) x d).card = (side K x d).card - 1 := by
    rw [hA1]
    exact Finset.card_erase_of_mem hw
  have hcol := colour_b_gen a b χ d (K.erase w) x
    (above_sub (Finset.erase_subset w K) hag)
    (by rw [hc1]; omega) (by rw [hA2]; exact he) (by rw [hc1]; omega)
  have hcard : (K.erase w).card = k + 1 := by
    have := Finset.card_erase_of_mem hwK
    omega
  exact hab ((hm _ (Finset.erase_subset w K) hcard).symm.trans hcol)

lemma one_side {X C : Type*} [LinearOrder X] [Fintype X]
    (k : ℕ) (hk : 5 ≤ k) (a b : C) (hab : a ≠ b) (χ : Finset X → C)
    (K : Finset (X → Bool)) (x : X) (d : Bool) (hag : Above K x)
    (hKc : K.card = k + 2) (hnc : ¬ Cat K)
    (hd : (side K x d).card = 1) (he : (side K x (!d)).card = k + 1)
    (hm : ∀ A : Finset (X → Bool), A ⊆ K → A.card = k + 1 →
      colour a b χ A = a) : False := by
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hd
  have hzs : z ∈ side K x d := by
    rw [hz]
    exact Finset.mem_singleton_self z
  obtain ⟨hzK, hzx⟩ := (mem_side K x d z).mp hzs
  have hcE : Cat (side K x (!d)) := by
    by_contra hE
    obtain ⟨W, hWE, hWc, hWb⟩ := bad_four _ hE
    have hsd := Finset.card_sdiff_add_card_eq_card hWE
    obtain ⟨v, hv⟩ :=
      Finset.card_pos.mp (show 0 < (side K x (!d) \ W).card by omega)
    obtain ⟨hvE, hvW⟩ := Finset.mem_sdiff.mp hv
    obtain ⟨hvK, hvx⟩ := (mem_side K x (!d) v).mp hvE
    have hWA : W ⊆ K.erase v := by
      intro u hu
      refine Finset.mem_erase.mpr ⟨?_, (side_subset K x (!d)) (hWE hu)⟩
      intro huv
      rw [huv] at hu
      exact hvW hu
    have hAnc : ¬ Cat (K.erase v) := fun hc => hc W hWA hWc hWb
    obtain ⟨u, hu⟩ := Finset.card_pos.mp (show 0 < W.card by omega)
    have hux := ((mem_side K x (!d) u).mp (hWE hu)).2
    have hzA : z ∈ K.erase v := by
      refine Finset.mem_erase.mpr ⟨?_, hzK⟩
      intro h
      rw [h] at hzx
      rw [hzx] at hvx
      exact not_ne d hvx.symm
    have hsplit : Split (K.erase v) x :=
      ⟨above_sub (Finset.erase_subset v K) hag, z, hzA, u, hWA hu,
        by rw [hzx, hux]; exact (not_ne d).symm⟩
    have hsmall : (side (K.erase v) x d).card < 3 := by
      rw [side_erase]
      have := Finset.card_le_card (Finset.erase_subset v (side K x d))
      omega
    have hcol := colour_b a b χ (K.erase v) hAnc (not_odd_small d hsplit hsmall)
    have hcard : (K.erase v).card = k + 1 := by
      have := Finset.card_erase_of_mem hvK
      omega
    exact hab ((hm _ (Finset.erase_subset v K) hcard).symm.trans hcol)
  obtain ⟨D, hDK, hcD, hDc⟩ := attach_side K x hag (!d) z hzK
    (by rw [hzx]; exact (not_ne d).symm) (side K x (!d))
    (Finset.Subset.refl _) hcE
  have hDe : D = K := Finset.eq_of_subset_of_card_le hDK (by omega)
  rw [hDe] at hcD
  exact hnc hcD

lemma a_core {X C : Type*} [LinearOrder X] [Fintype X]
    (k : ℕ) (hk : 5 ≤ k) (hodd : k % 2 = 1) (a b : C) (hab : a ≠ b)
    (χ : Finset X → C) (K : Finset (X → Bool))
    (hKc : K.card = k + 2) (hnc : ¬ Cat K)
    (hm : ∀ A : Finset (X → Bool), A ⊆ K → A.card = k + 1 →
      colour a b χ A = a) : False := by
  obtain ⟨x, hx⟩ := top K (by omega)
  obtain ⟨hp1, hp2⟩ := split_pos hx
  have hsum := side_card_sum K x
  by_cases hf : (side K x false).card % 2 = 1
  · by_cases hf1 : (side K x false).card = 1
    · exact one_side k hk a b hab χ K x false hx.1 hKc hnc hf1
        (show (side K x true).card = k + 1 by omega) hm
    · exact even_case k a b hab χ K x false hx.1 hKc (by omega) hf
        (show 2 ≤ (side K x true).card by omega) hm
  · have ht : (side K x true).card % 2 = 1 := by omega
    by_cases ht1 : (side K x true).card = 1
    · exact one_side k hk a b hab χ K x true hx.1 hKc hnc ht1
        (show (side K x false).card = k + 1 by omega) hm
    · exact even_case k a b hab χ K x true hx.1 hKc (by omega) ht
        (show 2 ≤ (side K x false).card by omega) hm

lemma choose_m (k f t : ℕ) (hk : 5 ≤ k) (hodd : k % 2 = 1)
    (hf : 3 ≤ f) (ht : 3 ≤ t) (hs : k + 3 ≤ f + t) :
    ∃ m, 3 ≤ m ∧ m ≤ f ∧ m + 3 ≤ k + 1 ∧ m % 2 = 1 ∧ k + 1 - m ≤ t := by
  by_cases h1 : k + 1 - t ≤ 3
  · exact ⟨3, by omega, by omega, by omega, by omega, by omega⟩
  · by_cases h2 : (k + 1 - t) % 2 = 1
    · exact ⟨k + 1 - t, by omega, by omega, by omega, by omega, by omega⟩
    · exact ⟨k + 2 - t, by omega, by omega, by omega, by omega, by omega⟩

lemma b_split {X C : Type*} [LinearOrder X] [Fintype X]
    (k : ℕ) (hk : 5 ≤ k) (hodd : k % 2 = 1) (a b : C) (χ : Finset X → C)
    (K : Finset (X → Bool)) (x : X) (hx : Split K x)
    (hf : 3 ≤ (side K x false).card) (ht : 3 ≤ (side K x true).card)
    (hs : k + 3 ≤ K.card) :
    ∃ A : Finset (X → Bool), A ⊆ K ∧ A.card = k + 1 ∧ colour a b χ A = a := by
  have hsum := side_card_sum K x
  obtain ⟨m, hm3, hmf, hmk, hmo, hmt⟩ :=
    choose_m k (side K x false).card (side K x true).card hk hodd hf ht (by omega)
  obtain ⟨P, hPK, hPc, hP⟩ := choose_side K x false m hmf
  obtain ⟨Q, hQK, hQc, hQ⟩ := choose_side K x true (k + 1 - m) hmt
  have hd := bits_disjoint x P Q hP hQ
  have he := sides_union x P Q hP hQ
  have hAK : P ∪ Q ⊆ K := Finset.union_subset hPK hQK
  have hAc : (P ∪ Q).card = k + 1 := by
    rw [Finset.card_union_of_disjoint hd, hPc, hQc]
    omega
  have hag : Above (P ∪ Q) x := above_sub hAK hx.1
  have hf' : (side (P ∪ Q) x false).card = m := by rw [he.1, hPc]
  have ht' : (side (P ∪ Q) x true).card = k + 1 - m := by rw [he.2, hQc]
  refine ⟨P ∪ Q, hAK, hAc, ?_⟩
  apply colour_a a b χ _ (noncat_sides hag (by omega) (by omega))
  exact ⟨x, split_of_pos hag (by omega) (by omega),
    by omega, by omega, by omega, by omega⟩

lemma b_extract {X C : Type*} [LinearOrder X] [Fintype X]
    (k : ℕ) (hk : 5 ≤ k) (hodd : k % 2 = 1) (a b : C) (hab : a ≠ b)
    (χ : Finset X → C) :
    ∀ n : ℕ, ∀ K : Finset (X → Bool), K.card ≤ n →
      (∀ A : Finset (X → Bool), A ⊆ K → A.card = k + 1 → colour a b χ A = b) →
      ∃ T : Finset (X → Bool), T ⊆ K ∧ Cat T ∧ K.card ≤ 2 * T.card + k := by
  intro n
  induction n with
  | zero =>
      intro K hK _
      exact ⟨∅, Finset.empty_subset K, cat_small ∅ (by simp), by omega⟩
  | succ n ih =>
      intro K hKn hm
      by_cases hsmall : K.card ≤ 3
      · exact ⟨K, Finset.Subset.refl K, cat_small K hsmall, by omega⟩
      by_cases hmid : K.card ≤ k + 2
      · obtain ⟨T, hT, hTc⟩ :=
          Finset.exists_subset_card_eq (show 3 ≤ K.card by omega)
        exact ⟨T, hT, cat_small T (by omega), by omega⟩
      obtain ⟨x, hx⟩ := top K (by omega)
      obtain ⟨hp1, hp2⟩ := split_pos hx
      have hsum := side_card_sum K x
      obtain ⟨zf, hzf⟩ := Finset.card_pos.mp hp1
      obtain ⟨hzfK, hzff⟩ := (mem_side K x false zf).mp hzf
      obtain ⟨zt, hzt⟩ := Finset.card_pos.mp hp2
      obtain ⟨hztK, hztt⟩ := (mem_side K x true zt).mp hzt
      have hzf' : zf x ≠ true := by rw [hzff]; decide
      have hzt' : zt x ≠ false := by rw [hztt]; decide
      by_cases hl : (side K x false).card ≤ 2
      · obtain ⟨T', hT'B, hcT', hT'c⟩ := ih (side K x true) (by omega)
          (fun A hA hAc => hm A (hA.trans (side_subset K x true)) hAc)
        obtain ⟨T, hTK, hcT, hTc⟩ :=
          attach_side K x hx.1 true zf hzfK hzf' T' hT'B hcT'
        exact ⟨T, hTK, hcT, by omega⟩
      by_cases hr : (side K x true).card ≤ 2
      · obtain ⟨T', hT'B, hcT', hT'c⟩ := ih (side K x false) (by omega)
          (fun A hA hAc => hm A (hA.trans (side_subset K x false)) hAc)
        obtain ⟨T, hTK, hcT, hTc⟩ :=
          attach_side K x hx.1 false zt hztK hzt' T' hT'B hcT'
        exact ⟨T, hTK, hcT, by omega⟩
      exfalso
      obtain ⟨A, hAK, hAc, hAa⟩ :=
        b_split k hk hodd a b χ K x hx (by omega) (by omega) (by omega)
      exact hab (hAa.symm.trans (hm A hAK hAc))

lemma cat_bound {X C : Type*} [LinearOrder X] [Fintype X]
    (k s : ℕ) (a b : C) (χ : Finset X → C) (i : C)
    (hχ : Solon.NoMono χ k s i)
    (K : Finset (X → Bool))
    (hm : ∀ A : Finset (X → Bool), A ⊆ K → A.card = k + 1 → colour a b χ A = i)
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
  rw [colour_cat a b χ A (cat_sub hAD hc), hAt] at hcol
  exact hne hcol

end OddStep

theorem odd_split_stepping_up : ∀ {X C : Type*} [LinearOrder X] [Fintype X] [DecidableEq C] (k : ℕ), 5 ≤ k → k % 2 = 1 → ∀ (a b : C), a ≠ b → ∀ (s : C → ℕ), (∀ i, k + 1 ≤ s i) → ∀ χ : Finset X → C, (∀ i, Solon.NoMono χ k (s i) i) → ∃ ψ : Finset (X → Bool) → C, Solon.NoMono ψ (k + 1) (s a + 1) a ∧ Solon.NoMono ψ (k + 1) (2 * s b + k + 1) b ∧ ∀ i, i ≠ a → i ≠ b → Solon.NoMono ψ (k + 1) (s i + 1) i := by
  intro X C _ _ _ k hk hodd a b hab s hs χ hχ
  refine ⟨OddStep.colour a b χ, ?_, ?_, ?_⟩
  · intro K hK
    by_contra hn
    have hm : ∀ A : Finset (X → Bool), A ⊆ K → A.card = k + 1 →
        OddStep.colour a b χ A = a := by
      intro A hA hc
      by_contra hne
      exact hn ⟨A, Finset.mem_powersetCard.mpr ⟨hA, hc⟩, hne⟩
    have hsa := hs a
    by_cases hcK : OddStep.Cat K
    · have := OddStep.cat_bound k (s a) a b χ a (hχ a) K hm K
        (Finset.Subset.refl K) hcK
      omega
    · obtain ⟨W, hWK, hWc, hWb⟩ := OddStep.bad_four K hcK
      obtain ⟨K', hWK', hK'K, hK'c⟩ :=
        OddStep.extend W K (k + 2) hWK (by omega) (by omega)
      exact OddStep.a_core k hk hodd a b hab χ K' hK'c
        (fun hc => hc W hWK' hWc hWb)
        (fun A hA hAc => hm A (hA.trans hK'K) hAc)
  · intro K hK
    by_contra hn
    have hm : ∀ A : Finset (X → Bool), A ⊆ K → A.card = k + 1 →
        OddStep.colour a b χ A = b := by
      intro A hA hc
      by_contra hne
      exact hn ⟨A, Finset.mem_powersetCard.mpr ⟨hA, hc⟩, hne⟩
    obtain ⟨T, hTK, hcT, hTc⟩ :=
      OddStep.b_extract k hk hodd a b hab χ K.card K (le_refl _) hm
    have := OddStep.cat_bound k (s b) a b χ b (hχ b) K hm T hTK hcT
    omega
  · intro i hia hib K hK
    by_contra hn
    have hm : ∀ A : Finset (X → Bool), A ⊆ K → A.card = k + 1 →
        OddStep.colour a b χ A = i := by
      intro A hA hc
      by_contra hne
      exact hn ⟨A, Finset.mem_powersetCard.mpr ⟨hA, hc⟩, hne⟩
    have hsi := hs i
    have hcK : OddStep.Cat K := by
      apply OddStep.cat_local (k + 1) (by omega) K (by omega)
      intro A hAK hAc
      by_contra hnc
      rcases OddStep.colour_noncat a b χ A hnc with h | h
      · exact hia ((hm A hAK hAc).symm.trans h)
      · exact hib ((hm A hAK hAc).symm.trans h)
    have := OddStep.cat_bound k (s i) a b χ i (hχ i) K hm K
      (Finset.Subset.refl K) hcK
    omega

