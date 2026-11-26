import Proofs.Defs

set_option maxHeartbeats 0
set_option maxRecDepth 4096

open Classical

namespace SharpThin

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

lemma bool_ne_false : ∀ b : Bool, b ≠ false → b = true := by
  intro b
  cases b <;> decide

lemma bool_ne_true : ∀ b : Bool, b ≠ true → b = false := by
  intro b
  cases b <;> decide

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
  refine ⟨S ∪ R, Finset.subset_union_left,
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

lemma side_union {X : Type*} [DecidableEq (X → Bool)]
    (A : Finset (X → Bool)) (x : X) :
    side A x false ∪ side A x true = A := by
  ext v
  simp only [Finset.mem_union, mem_side]
  constructor
  · rintro (⟨hv, _⟩ | ⟨hv, _⟩) <;> exact hv
  · intro hv
    rcases bool_cases (v x) with h | h
    · exact Or.inl ⟨hv, h⟩
    · exact Or.inr ⟨hv, h⟩

lemma side_card_sum {X : Type*}
    (A : Finset (X → Bool)) (x : X) :
    (side A x false).card + (side A x true).card = A.card := by
  have hd : Disjoint (side A x false) (side A x true) := by
    rw [Finset.disjoint_left]
    intro v hv hw
    exact ft (((mem_side A x false v).mp hv).2.symm.trans
      ((mem_side A x true v).mp hw).2)
  rw [← Finset.card_union_of_disjoint hd, side_union A x]

lemma disj_gen {X : Type*}
    (d : Bool) (x : X) (P Q : Finset (X → Bool))
    (hP : ∀ v ∈ P, v x = d)
    (hQ : ∀ v ∈ Q, v x ≠ d) : Disjoint P Q := by
  rw [Finset.disjoint_left]
  intro v hv hw
  exact hQ v hw (hP v hv)

lemma bits_disjoint {X : Type*}
    (x : X) (P Q : Finset (X → Bool))
    (hP : ∀ v ∈ P, v x = false)
    (hQ : ∀ v ∈ Q, v x = true) : Disjoint P Q := by
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
    {A : Finset (X → Bool)} {x : X} (h : Split A x) :
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

lemma attach_side {X : Type*} [LinearOrder X] [Fintype X]
    (K : Finset (X → Bool)) (x : X) (hag : Above K x)
    (d : Bool) (z : X → Bool) (hz : z ∈ K) (hzd : z x ≠ d)
    (T : Finset (X → Bool)) (hT : T ⊆ side K x d) (hc : Cat T) :
    ∃ D : Finset (X → Bool),
      D ⊆ K ∧ Cat D ∧ D.card = T.card + 1 := by
  have hTK : T ⊆ K := hT.trans (side_subset K x d)
  have hzT : z ∉ T := fun h =>
    hzd ((mem_side K x d z).mp (hT h)).2
  have hr : ∀ w ∈ T,
      w x ≠ z x ∧ ∀ y, x < y → w y = z y := by
    intro w hw
    have hwd := ((mem_side K x d w).mp (hT hw)).2
    refine ⟨?_, fun y hy => hag w (hTK hw) z hz y hy⟩
    intro he
    exact hzd (he.symm.trans hwd)
  exact ⟨insert z T, Finset.insert_subset hz hTK,
    cat_insert z T x hr hc, Finset.card_insert_of_notMem hzT⟩

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

lemma maximum_exists {X : Type*} [LinearOrder X] [Fintype X]
    (A : Finset (X → Bool)) :
    ∃ T : Finset (X → Bool), T ⊆ A ∧ Cat T ∧
      ∀ U : Finset (X → Bool), U ⊆ A → Cat U → U.card ≤ T.card := by
  let P := A.powerset.filter Cat
  have he : (∅ : Finset (X → Bool)) ∈ P :=
    Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.empty_subset A),
        cat_small ∅ (by simp)⟩
  obtain ⟨T, hT, hmax⟩ :=
    Finset.exists_max_image P Finset.card ⟨∅, he⟩
  obtain ⟨hTA, hcT⟩ := Finset.mem_filter.mp hT
  refine ⟨T, Finset.mem_powerset.mp hTA, hcT, ?_⟩
  intro U hUA hcU
  exact hmax U
    (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hUA, hcU⟩)

noncomputable def best {X : Type*} [LinearOrder X] [Fintype X]
    (A : Finset (X → Bool)) : Finset (X → Bool) :=
  Classical.choose (maximum_exists A)

noncomputable def rank {X : Type*} [LinearOrder X] [Fintype X]
    (A : Finset (X → Bool)) : ℕ :=
  (best A).card

lemma best_spec {X : Type*} [LinearOrder X] [Fintype X]
    (A : Finset (X → Bool)) :
    best A ⊆ A ∧ Cat (best A) ∧
      ∀ U : Finset (X → Bool), U ⊆ A → Cat U →
        U.card ≤ (best A).card :=
  Classical.choose_spec (maximum_exists A)

lemma cat_le_rank {X : Type*} [LinearOrder X] [Fintype X]
    (A B : Finset (X → Bool)) (hAB : A ⊆ B) (hc : Cat A) :
    A.card ≤ rank B :=
  (best_spec B).2.2 A hAB hc

lemma rank_le {X : Type*} [LinearOrder X] [Fintype X]
    (A : Finset (X → Bool)) : rank A ≤ A.card :=
  Finset.card_le_card (best_spec A).1

lemma rank_eq_of_cat {X : Type*} [LinearOrder X] [Fintype X]
    (A : Finset (X → Bool)) (hc : Cat A) : rank A = A.card :=
  Nat.le_antisymm (rank_le A)
    (cat_le_rank A A (Finset.Subset.refl A) hc)

lemma cat_of_rank_eq {X : Type*} [LinearOrder X] [Fintype X]
    (A : Finset (X → Bool)) (h : rank A = A.card) : Cat A := by
  have he : best A = A :=
    Finset.eq_of_subset_of_card_le (best_spec A).1
      (by change A.card ≤ rank A; omega)
  have hc := (best_spec A).2.1
  rwa [he] at hc

lemma rank_small {X : Type*} [LinearOrder X] [Fintype X]
    (A : Finset (X → Bool)) (hA : A.card ≤ 3) :
    rank A = A.card :=
  rank_eq_of_cat A (cat_small A hA)

lemma rank_ge_three {X : Type*} [LinearOrder X] [Fintype X]
    (A : Finset (X → Bool)) (hA : 3 ≤ A.card) : 3 ≤ rank A := by
  obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq hA
  have hh := cat_le_rank T A hT (cat_small T (by omega))
  omega

lemma rank_split {X : Type*} [LinearOrder X] [Fintype X]
    (K : Finset (X → Bool)) (x : X) (hx : Split K x) :
    rank K = max (rank (side K x false)) (rank (side K x true)) + 1 := by
  have hp := split_pos hx
  have lower (d : Bool) (z : X → Bool)
      (hz : z ∈ K) (hzd : z x ≠ d) :
      rank (side K x d) + 1 ≤ rank K := by
    obtain ⟨D, hDK, hcD, hDc⟩ :=
      attach_side K x hx.1 d z hz hzd
        (best (side K x d)) (best_spec _).1 (best_spec _).2.1
    have hh := cat_le_rank D K hDK hcD
    change D.card = rank (side K x d) + 1 at hDc
    omega
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hp.1
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hp.2
  obtain ⟨huK, huf⟩ := (mem_side K x false u).mp hu
  obtain ⟨hvK, hvt⟩ := (mem_side K x true v).mp hv
  have hl := lower false v hvK (by rw [hvt]; decide)
  have hr := lower true u huK (by rw [huf]; decide)
  have hT := best_spec K
  have hs := cat_split hT.2.1 (above_sub hT.1 hx.1)
  have hsum := side_card_sum (best K) x
  change (side (best K) x false).card +
    (side (best K) x true).card = rank K at hsum
  have bound (d : Bool) :
      (side (best K) x d).card ≤ rank (side K x d) := by
    apply cat_le_rank
    · intro w hw
      obtain ⟨hwT, hwd⟩ := (mem_side (best K) x d w).mp hw
      exact (mem_side K x d w).mpr ⟨hT.1 hwT, hwd⟩
    · exact cat_sub (side_subset (best K) x d) hT.2.1
  have hbf := bound false
  have hbt := bound true
  omega

lemma rank_union {X : Type*} [LinearOrder X] [Fintype X]
    (d : Bool) (x : X) (P Q : Finset (X → Bool))
    (hag : Above (P ∪ Q) x)
    (hP : ∀ v ∈ P, v x = d)
    (hQ : ∀ v ∈ Q, v x ≠ d)
    (hp : 0 < P.card) (hq : 0 < Q.card) :
    rank (P ∪ Q) = max (rank P) (rank Q) + 1 := by
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hp
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hq
  have hx : Split (P ∪ Q) x :=
    ⟨hag, u, Finset.mem_union_left _ hu,
      v, Finset.mem_union_right _ hv,
      fun h => hQ v hv (h.symm.trans (hP u hu))⟩
  have hr := rank_split (P ∪ Q) x hx
  cases d
  · have he := sides_union x P Q hP
      (fun w hw => bool_ne_false _ (hQ w hw))
    rw [he.1, he.2] at hr
    exact hr
  · have he := sides_union x Q P
      (fun w hw => bool_ne_true _ (hQ w hw)) hP
    have hf : side (P ∪ Q) x false = Q := by
      rw [Finset.union_comm]
      exact he.1
    have ht : side (P ∪ Q) x true = P := by
      rw [Finset.union_comm]
      exact he.2
    rw [hf, ht, max_comm] at hr
    exact hr

lemma rank_ge_four {X : Type*} [LinearOrder X] [Fintype X]
    (K : Finset (X → Bool)) (hK : 5 ≤ K.card) : 4 ≤ rank K := by
  obtain ⟨x, hx⟩ := top K (by omega)
  have hp := split_pos hx
  have hs := side_card_sum K x
  have hr := rank_split K x hx
  by_cases hf : 3 ≤ (side K x false).card
  · have hh := rank_ge_three (side K x false) hf
    omega
  · have hh := rank_ge_three (side K x true) (by omega)
    omega

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

def Thin {X : Type*} [LinearOrder X]
    (A : Finset (X → Bool)) : Prop :=
  ∃ x : X, Split A x ∧
    (((side A x false).card = 2 ∧ ¬ Cat (side A x true)) ∨
     ((side A x true).card = 2 ∧ ¬ Cat (side A x false)))

noncomputable def colour {X C : Type*} [LinearOrder X] [Fintype X]
    (a b : C) (χ : Finset X → C)
    (A : Finset (X → Bool)) : C :=
  if Cat A then χ (levels A) else if Thin A then a else b

lemma colour_cat {X C : Type*} [LinearOrder X] [Fintype X]
    (a b : C) (χ : Finset X → C)
    (A : Finset (X → Bool)) (hc : Cat A) :
    colour a b χ A = χ (levels A) := by
  unfold colour
  rw [if_pos hc]

lemma colour_a {X C : Type*} [LinearOrder X] [Fintype X]
    (a b : C) (χ : Finset X → C)
    (A : Finset (X → Bool)) (hc : ¬ Cat A) (ht : Thin A) :
    colour a b χ A = a := by
  unfold colour
  rw [if_neg hc, if_pos ht]

lemma colour_b {X C : Type*} [LinearOrder X] [Fintype X]
    (a b : C) (χ : Finset X → C)
    (A : Finset (X → Bool)) (hc : ¬ Cat A) (ht : ¬ Thin A) :
    colour a b χ A = b := by
  unfold colour
  rw [if_neg hc, if_neg ht]

lemma colour_red_parts {X C : Type*} [LinearOrder X] [Fintype X]
    (a b : C) (χ : Finset X → C)
    (d : Bool) (P Q : Finset (X → Bool)) (x : X)
    (hag : Above (P ∪ Q) x)
    (hP : ∀ v ∈ P, v x = d) (hQ : ∀ v ∈ Q, v x ≠ d)
    (hp : 0 < P.card) (hq : 0 < Q.card)
    (hcase : (P.card = 2 ∧ ¬ Cat Q) ∨
      (Q.card = 2 ∧ ¬ Cat P)) :
    colour a b χ (P ∪ Q) = a := by
  have hnc : ¬ Cat (P ∪ Q) := by
    intro hc
    rcases hcase with ⟨_, hn⟩ | ⟨_, hn⟩
    · exact hn (cat_sub Finset.subset_union_right hc)
    · exact hn (cat_sub Finset.subset_union_left hc)
  apply colour_a a b χ (P ∪ Q) hnc
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hp
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hq
  have hx : Split (P ∪ Q) x :=
    ⟨hag, u, Finset.mem_union_left _ hu,
      v, Finset.mem_union_right _ hv,
      fun h => hQ v hv (h.symm.trans (hP u hu))⟩
  refine ⟨x, hx, ?_⟩
  cases d
  · have he := sides_union x P Q hP
      (fun w hw => bool_ne_false _ (hQ w hw))
    rw [he.1, he.2]
    exact hcase
  · have he := sides_union x Q P
      (fun w hw => bool_ne_true _ (hQ w hw)) hP
    rw [Finset.union_comm P Q, he.1, he.2]
    rcases hcase with h | h
    · exact Or.inr h
    · exact Or.inl h

lemma colour_blue_parts {X C : Type*} [LinearOrder X] [Fintype X]
    (a b : C) (χ : Finset X → C)
    (d : Bool) (P Q : Finset (X → Bool)) (x : X)
    (hag : Above (P ∪ Q) x)
    (hP : ∀ v ∈ P, v x = d) (hQ : ∀ v ∈ Q, v x ≠ d)
    (hp : 0 < P.card) (hq : 0 < Q.card)
    (hP2 : P.card = 2 → Cat Q)
    (hQ2 : Q.card = 2 → Cat P)
    (hnc : ¬ Cat (P ∪ Q)) :
    colour a b χ (P ∪ Q) = b := by
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hp
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hq
  have hx : Split (P ∪ Q) x :=
    ⟨hag, u, Finset.mem_union_left _ hu,
      v, Finset.mem_union_right _ hv,
      fun h => hQ v hv (h.symm.trans (hP u hu))⟩
  have hnot : ¬ (((side (P ∪ Q) x false).card = 2 ∧
        ¬ Cat (side (P ∪ Q) x true)) ∨
      ((side (P ∪ Q) x true).card = 2 ∧
        ¬ Cat (side (P ∪ Q) x false))) := by
    cases d
    · have he := sides_union x P Q hP
        (fun w hw => bool_ne_false _ (hQ w hw))
      rw [he.1, he.2]
      rintro (⟨h2, hc⟩ | ⟨h2, hc⟩)
      · exact hc (hP2 h2)
      · exact hc (hQ2 h2)
    · have he := sides_union x Q P
        (fun w hw => bool_ne_true _ (hQ w hw)) hP
      rw [Finset.union_comm P Q, he.1, he.2]
      rintro (⟨h2, hc⟩ | ⟨h2, hc⟩)
      · exact hc (hQ2 h2)
      · exact hc (hP2 h2)
  apply colour_b a b χ (P ∪ Q) hnc
  rintro ⟨y, hy, ht⟩
  have hyx : y = x := split_unique hy hx
  subst y
  exact hnot ht

lemma cat_bound {X C : Type*} [LinearOrder X] [Fintype X]
    (a b : C) (χ : Finset X → C) (i : C) (s : ℕ)
    (hχ : Solon.NoMono χ 6 s i)
    (K : Finset (X → Bool))
    (hm : ∀ A : Finset (X → Bool),
      A ⊆ K → A.card = 7 → colour a b χ A = i)
    (D : Finset (X → Bool)) (hDK : D ⊆ K) (hc : Cat D) :
    D.card ≤ s := by
  by_contra hbig
  have hh := cat_card D.card D (le_refl _) hc
  obtain ⟨S, hS, hSc⟩ :=
    Finset.exists_subset_card_eq
      (show s ≤ (levels D).card by omega)
  obtain ⟨T, hT, hne⟩ := hχ S hSc
  obtain ⟨hTS, hTc⟩ := Finset.mem_powersetCard.mp hT
  have hDn : D.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨A, hAD, hAc, hAt⟩ :=
    realise D.card D (le_refl _) hc hDn T (hTS.trans hS)
  have hcol := hm A (hAD.trans hDK) (by omega)
  rw [colour_cat a b χ A (cat_sub hAD hc), hAt] at hcol
  exact hne hcol

lemma rank_bound {X C : Type*} [LinearOrder X] [Fintype X]
    (a b : C) (χ : Finset X → C) (i : C) (s : ℕ)
    (hχ : Solon.NoMono χ 6 s i)
    (K : Finset (X → Bool))
    (hm : ∀ A : Finset (X → Bool),
      A ⊆ K → A.card = 7 → colour a b χ A = i) :
    rank K ≤ s :=
  cat_bound a b χ i s hχ K hm (best K)
    (best_spec K).1 (best_spec K).2.1

lemma red_middle {X C : Type*} [LinearOrder X] [Fintype X]
    (a b : C) (hab : a ≠ b) (χ : Finset X → C)
    (K L R : Finset (X → Bool)) (x : X) (d : Bool)
    (hag : Above K x) (hLK : L ⊆ K) (hRK : R ⊆ K)
    (hL : ∀ v ∈ L, v x = d) (hR : ∀ v ∈ R, v x ≠ d)
    (hLc : 4 ≤ L.card) (hRc : 3 ≤ R.card)
    (hm : ∀ A : Finset (X → Bool),
      A ⊆ K → A.card = 7 → colour a b χ A = a) : False := by
  obtain ⟨P, hPL, hPc⟩ := Finset.exists_subset_card_eq hLc
  obtain ⟨Q, hQR, hQc⟩ := Finset.exists_subset_card_eq hRc
  have hP : ∀ v ∈ P, v x = d := fun v hv => hL v (hPL hv)
  have hQ : ∀ v ∈ Q, v x ≠ d := fun v hv => hR v (hQR hv)
  have hAK : P ∪ Q ⊆ K :=
    Finset.union_subset (hPL.trans hLK) (hQR.trans hRK)
  have hAc : (P ∪ Q).card = 7 := by
    rw [Finset.card_union_of_disjoint (disj_gen d x P Q hP hQ),
      hPc, hQc]
  have hnc : ¬ Cat (P ∪ Q) :=
    noncat_parts d (P ∪ Q) P Q x (above_sub hAK hag)
      Finset.subset_union_left Finset.subset_union_right
      hP hQ (by omega) (by omega)
  have hb := colour_blue_parts a b χ d P Q x
    (above_sub hAK hag) hP hQ (by omega) (by omega)
    (fun h => absurd h (by omega))
    (fun h => absurd h (by omega)) hnc
  exact hab ((hm _ hAK hAc).symm.trans hb)

lemma red_large {X C : Type*} [LinearOrder X] [Fintype X]
    (a b : C) (hab : a ≠ b) (χ : Finset X → C)
    (K L R : Finset (X → Bool)) (x : X) (d : Bool)
    (hag : Above K x) (he : L ∪ R = K)
    (hL : ∀ v ∈ L, v x = d) (hR : ∀ v ∈ R, v x ≠ d)
    (hLc : 6 ≤ L.card) (hRc : 0 < R.card)
    (hm : ∀ A : Finset (X → Bool),
      A ⊆ K → A.card = 7 → colour a b χ A = a) : Cat K := by
  have hLK : L ⊆ K := by
    rw [← he]
    exact Finset.subset_union_left
  have hRK : R ⊆ K := by
    rw [← he]
    exact Finset.subset_union_right
  obtain ⟨z, hzR⟩ := Finset.card_pos.mp hRc
  have hcL : Cat L := by
    by_contra hn
    obtain ⟨W, hWL, hWc, hWb⟩ := bad_four L hn
    obtain ⟨P, hWP, hPL, hPc⟩ :=
      extend W L 6 hWL (by omega) hLc
    have hP : ∀ v ∈ P, v x = d := fun v hv => hL v (hPL hv)
    have hZ : ∀ v ∈ ({z} : Finset (X → Bool)), v x ≠ d := by
      intro v hv
      rw [Finset.mem_singleton.mp hv]
      exact hR z hzR
    have hZc : ({z} : Finset (X → Bool)).card = 1 := by simp
    have hZK : ({z} : Finset (X → Bool)) ⊆ K :=
      Finset.singleton_subset_iff.mpr (hRK hzR)
    have hAK : P ∪ {z} ⊆ K :=
      Finset.union_subset (hPL.trans hLK) hZK
    have hAc : (P ∪ {z}).card = 7 := by
      rw [Finset.card_union_of_disjoint (disj_gen d x P {z} hP hZ),
        hPc, hZc]
    have hnc : ¬ Cat (P ∪ {z}) := by
      intro hc
      exact hc W (hWP.trans Finset.subset_union_left) hWc hWb
    have hb := colour_blue_parts a b χ d P {z} x
      (above_sub hAK hag) hP hZ (by omega) (by omega)
      (fun h => absurd h (by omega))
      (fun h => absurd h (by omega)) hnc
    exact hab ((hm _ hAK hAc).symm.trans hb)
  have hRsmall : R.card ≤ 1 := by
    by_contra hn
    obtain ⟨P, hPL, hPc⟩ :=
      Finset.exists_subset_card_eq (show 5 ≤ L.card by omega)
    obtain ⟨Q, hQR, hQc⟩ :=
      Finset.exists_subset_card_eq (show 2 ≤ R.card by omega)
    have hP : ∀ v ∈ P, v x = d := fun v hv => hL v (hPL hv)
    have hQ : ∀ v ∈ Q, v x ≠ d := fun v hv => hR v (hQR hv)
    have hAK : P ∪ Q ⊆ K :=
      Finset.union_subset (hPL.trans hLK) (hQR.trans hRK)
    have hAc : (P ∪ Q).card = 7 := by
      rw [Finset.card_union_of_disjoint (disj_gen d x P Q hP hQ),
        hPc, hQc]
    have hnc : ¬ Cat (P ∪ Q) :=
      noncat_parts d (P ∪ Q) P Q x (above_sub hAK hag)
        Finset.subset_union_left Finset.subset_union_right
        hP hQ (by omega) (by omega)
    have hb := colour_blue_parts a b χ d P Q x
      (above_sub hAK hag) hP hQ (by omega) (by omega)
      (fun h => absurd h (by omega))
      (fun _ => cat_sub hPL hcL) hnc
    exact hab ((hm _ hAK hAc).symm.trans hb)
  have hsum : L.card + R.card = K.card := by
    rw [← Finset.card_union_of_disjoint (disj_gen d x L R hL hR), he]
  have hKr := rank_union d x L R (by rw [he]; exact hag)
    hL hR (by omega) hRc
  rw [he] at hKr
  have hLr := rank_eq_of_cat L hcL
  have hRr := rank_small R (by omega)
  exact cat_of_rank_eq K (by omega)

lemma red_structure {X C : Type*} [LinearOrder X] [Fintype X]
    (a b : C) (hab : a ≠ b) (χ : Finset X → C)
    (K : Finset (X → Bool)) (hK : 8 ≤ K.card)
    (hm : ∀ A : Finset (X → Bool),
      A ⊆ K → A.card = 7 → colour a b χ A = a) : Cat K := by
  obtain ⟨x, hx⟩ := top K (by omega)
  have hp := split_pos hx
  have hs := side_card_sum K x
  have hf : ∀ v ∈ side K x false, v x = false :=
    fun v hv => ((mem_side K x false v).mp hv).2
  have ht : ∀ v ∈ side K x true, v x = true :=
    fun v hv => ((mem_side K x true v).mp hv).2
  have hnf : ∀ v ∈ side K x false, v x ≠ true := by
    intro v hv
    rw [hf v hv]
    decide
  have hnt : ∀ v ∈ side K x true, v x ≠ false := by
    intro v hv
    rw [ht v hv]
    decide
  by_cases hf6 : 6 ≤ (side K x false).card
  · exact red_large a b hab χ K
      (side K x false) (side K x true) x false hx.1
      (side_union K x) hf hnt hf6 hp.2 hm
  by_cases ht6 : 6 ≤ (side K x true).card
  · exact red_large a b hab χ K
      (side K x true) (side K x false) x true hx.1
      (by rw [Finset.union_comm]; exact side_union K x)
      ht hnf ht6 hp.1 hm
  by_cases hf4 : 4 ≤ (side K x false).card
  · exact (red_middle a b hab χ K
      (side K x false) (side K x true) x false hx.1
      (side_subset K x false) (side_subset K x true)
      hf hnt hf4 (by omega) hm).elim
  · exact (red_middle a b hab χ K
      (side K x true) (side K x false) x true hx.1
      (side_subset K x true) (side_subset K x false)
      ht hnf (by omega) (by omega) hm).elim

lemma blue_side_cat {X C : Type*} [LinearOrder X] [Fintype X]
    (a b : C) (hab : a ≠ b) (χ : Finset X → C)
    (K L R : Finset (X → Bool)) (x : X) (d : Bool)
    (hag : Above K x) (hLK : L ⊆ K) (hRK : R ⊆ K)
    (hL : ∀ v ∈ L, v x = d) (hR : ∀ v ∈ R, v x ≠ d)
    (hLc : 5 ≤ L.card) (hRc : 2 ≤ R.card)
    (hm : ∀ A : Finset (X → Bool),
      A ⊆ K → A.card = 7 → colour a b χ A = b) : Cat L := by
  by_contra hn
  obtain ⟨W, hWL, hWc, hWb⟩ := bad_four L hn
  obtain ⟨P, hWP, hPL, hPc⟩ :=
    extend W L 5 hWL (by omega) hLc
  obtain ⟨Q, hQR, hQc⟩ := Finset.exists_subset_card_eq hRc
  have hP : ∀ v ∈ P, v x = d := fun v hv => hL v (hPL hv)
  have hQ : ∀ v ∈ Q, v x ≠ d := fun v hv => hR v (hQR hv)
  have hAK : P ∪ Q ⊆ K :=
    Finset.union_subset (hPL.trans hLK) (hQR.trans hRK)
  have hAc : (P ∪ Q).card = 7 := by
    rw [Finset.card_union_of_disjoint (disj_gen d x P Q hP hQ),
      hPc, hQc]
  have hPn : ¬ Cat P := fun hc => hc W hWP hWc hWb
  have ha := colour_red_parts a b χ d P Q x
    (above_sub hAK hag) hP hQ (by omega) (by omega)
    (Or.inr ⟨hQc, hPn⟩)
  exact hab (ha.symm.trans (hm _ hAK hAc))

lemma blue_extract {X C : Type*} [LinearOrder X] [Fintype X]
    (a b : C) (hab : a ≠ b) (χ : Finset X → C) :
    ∀ n : ℕ, ∀ K : Finset (X → Bool), K.card ≤ n →
      (∀ A : Finset (X → Bool),
        A ⊆ K → A.card = 7 → colour a b χ A = b) →
      K.card + 2 ≤ 2 * rank K ∨ K.card ≤ rank K + 4 := by
  intro n
  induction n with
  | zero =>
      intro K hK _
      right
      omega
  | succ n ih =>
      intro K hKn hm
      by_cases hsmall : K.card ≤ 8
      · right
        by_cases hfour : K.card ≤ 4
        · omega
        · have hh := rank_ge_four K (by omega)
          omega
      obtain ⟨x, hx⟩ := top K (by omega)
      have hp := split_pos hx
      have hs := side_card_sum K x
      have hr := rank_split K x hx
      by_cases hf1 : (side K x false).card ≤ 1
      · have hh := ih (side K x true) (by omega)
          (fun A hA hAc =>
            hm A (hA.trans (side_subset K x true)) hAc)
        rcases hh with hh | hh
        · left
          omega
        · right
          omega
      by_cases ht1 : (side K x true).card ≤ 1
      · have hh := ih (side K x false) (by omega)
          (fun A hA hAc =>
            hm A (hA.trans (side_subset K x false)) hAc)
        rcases hh with hh | hh
        · left
          omega
        · right
          omega
      have hf : ∀ v ∈ side K x false, v x = false :=
        fun v hv => ((mem_side K x false v).mp hv).2
      have ht : ∀ v ∈ side K x true, v x = true :=
        fun v hv => ((mem_side K x true v).mp hv).2
      have hnf : ∀ v ∈ side K x false, v x ≠ true := by
        intro v hv
        rw [hf v hv]
        decide
      have hnt : ∀ v ∈ side K x true, v x ≠ false := by
        intro v hv
        rw [ht v hv]
        decide
      have hcF : 5 ≤ (side K x false).card → Cat (side K x false) := by
        intro h
        exact blue_side_cat a b hab χ K
          (side K x false) (side K x true) x false hx.1
          (side_subset K x false) (side_subset K x true)
          hf hnt h (by omega) hm
      have hcT : 5 ≤ (side K x true).card → Cat (side K x true) := by
        intro h
        exact blue_side_cat a b hab χ K
          (side K x true) (side K x false) x true hx.1
          (side_subset K x true) (side_subset K x false)
          ht hnf h (by omega) hm
      have hhigh : 6 ≤ rank K := by
        by_cases hF : 5 ≤ (side K x false).card
        · have hh := rank_eq_of_cat (side K x false) (hcF hF)
          omega
        · have hT : 5 ≤ (side K x true).card := by omega
          have hh := rank_eq_of_cat (side K x true) (hcT hT)
          omega
      have hFbound : (side K x false).card + 1 ≤ rank K := by
        by_cases hF : 5 ≤ (side K x false).card
        · have hh := rank_eq_of_cat (side K x false) (hcF hF)
          omega
        · omega
      have hTbound : (side K x true).card + 1 ≤ rank K := by
        by_cases hT : 5 ≤ (side K x true).card
        · have hh := rank_eq_of_cat (side K x true) (hcT hT)
          omega
        · omega
      left
      omega

end SharpThin

theorem six_uniform_sharp_thin_split :
    ∀ {X : Type*} [LinearOrder X] [Fintype X] (t : ℕ),
      7 ≤ t →
      ∀ χ : Finset X → Fin 2,
        Solon.NoMono χ 6 7 0 →
        Solon.NoMono χ 6 t 1 →
        ∃ ψ : Finset (X → Bool) → Fin 2,
          Solon.NoMono ψ 7 8 0 ∧
          Solon.NoMono ψ 7 (2 * t - 1) 1 := by
  intro X _ _ t ht χ hχ0 hχ1
  classical
  refine ⟨SharpThin.colour 0 1 χ, ?_, ?_⟩
  · intro K hK
    by_contra hn
    have hm : ∀ A : Finset (X → Bool),
        A ⊆ K → A.card = 7 → SharpThin.colour 0 1 χ A = 0 := by
      intro A hA hAc
      by_contra hne
      exact hn ⟨A, Finset.mem_powersetCard.mpr ⟨hA, hAc⟩, hne⟩
    have hc := SharpThin.red_structure 0 1 (by decide) χ K
      (by omega) hm
    have hb := SharpThin.cat_bound 0 1 χ 0 7 hχ0
      K hm K (Finset.Subset.refl K) hc
    omega
  · intro K hK
    by_contra hn
    have hm : ∀ A : Finset (X → Bool),
        A ⊆ K → A.card = 7 → SharpThin.colour 0 1 χ A = 1 := by
      intro A hA hAc
      by_contra hne
      exact hn ⟨A, Finset.mem_powersetCard.mpr ⟨hA, hAc⟩, hne⟩
    have hr := SharpThin.rank_bound 0 1 χ 1 t hχ1 K hm
    have hb := SharpThin.blue_extract 0 1 (by decide) χ
      K.card K (le_refl _) hm
    rcases hb with hb | hb <;> omega

