import Mathlib
/-!
# A400868 : sens facile, uniquement

Preuve par blocs de Claude (notes/SENS_FACILE_claude.md), relue et formalisée
par ChatGPT, le 2026-11-10.

`easy_direction` construit une donne équilibrée des cartes distinctes 1,...,n,
pour n>0 non puissance de 2, dont tous les états successifs sont non terminaux.
La règle remet la perdante avant la gagnante. Les blocs sont définis récursivement ;
`block_weave` prouve l'identité d'entrelacement utilisée dans la preuve papier.
Le rembobinage est construit directement sur un suffixe de paires de la famille,
puis la réalisation ordonnée en cartes distinctes est prouvée par un isomorphisme
entre un ordre fini d'occurrences étiquetées et Fin n.

Aucune assertion sur le sens difficile. Import autonome Mathlib.
Environnement : Lean 4.36.0-rc2, Mathlib
9d581dfff2e41de989072ea63abf3daf69311520.
-/
namespace A400868
abbrev State (α : Type*) := List α × List α

def live {α : Type*} (s : State α) : Prop := s.1 ≠ [] ∧ s.2 ≠ []
def step {α : Type*} [LinearOrder α] (s : State α) : State α :=
  match s with
  | (x::xs,y::ys) => if x< y then (xs,ys++[x,y]) else (xs++[y,x],ys)
  | _ => s
def run {α : Type*} [LinearOrder α] : ℕ → State α → State α
  | 0,s => s
  | k+1,s => run k (step s)
def NeverEnds {α : Type*} [LinearOrder α] (s : State α) : Prop := ∀ k, live (run k s)

inductive Turn {α : Type*} [LT α] : State α → State α → Prop
  | left {x y : α} {xs ys : List α} (h : y< x) : Turn (x::xs,y::ys) (xs++[y,x],ys)
  | right {x y : α} {xs ys : List α} (h : x< y) : Turn (x::xs,y::ys) (xs,ys++[x,y])
inductive Path {α : Type*} [LT α] : ℕ → State α → State α → Prop
  | zero (s) : Path 0 s s
  | cons {k s t u} : Turn s t → Path k t u → Path (k+1) s u

lemma turn_step {α : Type*} [LinearOrder α] {s t : State α} (h : Turn s t) : step s=t := by
  cases h with
  | left h => simp [step,not_lt_of_gt h]
  | right h => simp [step,h]
lemma turn_live {α : Type*} [LT α] {s t : State α} (h : Turn s t) : live s := by
  cases h <;> simp [live]
lemma turn_swap {α : Type*} [LT α] {s t : State α} (h : Turn s t) : Turn s.swap t.swap := by
  cases h with
  | left h => exact Turn.right h
  | right h => exact Turn.left h
lemma path_swap {α : Type*} [LT α] {k : ℕ} {s t : State α} (h : Path k s t) : Path k s.swap t.swap := by
  induction h with
  | zero s => exact Path.zero _
  | cons h hpath ih => exact Path.cons (turn_swap h) ih
lemma path_trans {α : Type*} [LT α] {k l : ℕ} {s t u : State α}
    (h : Path k s t) (g : Path l t u) : Path (k+l) s u := by
  induction h with
  | zero => simpa using g
  | cons ht hp ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Path.cons ht (ih g)
lemma path_run {α : Type*} [LinearOrder α] {k : ℕ} {s t : State α} (h : Path k s t) : run k s=t := by
  induction h with
  | zero => rfl
  | cons ht hp ih => simpa [run,turn_step ht] using ih
lemma path_prefix_live {α : Type*} [LinearOrder α] {k : ℕ} {s t : State α}
    (h : Path k s t) {j : ℕ} (hj : j< k) : live (run j s) := by
  induction h generalizing j with
  | zero => omega
  | cons ht hp ih =>
    cases j with
    | zero => exact turn_live ht
    | succ j => simpa [run,turn_step ht] using ih (by omega : j< _)
lemma loop_repeat {α : Type*} [LT α] {k : ℕ} {s : State α} (h : Path k s s) (r : ℕ) : Path (r*k) s s := by
  induction r with
  | zero => simpa using Path.zero s
  | succ r ih => simpa [Nat.succ_mul] using path_trans ih h
lemma neverEnds_of_loop {α : Type*} [LinearOrder α] {k : ℕ} {s : State α}
    (hk : 0< k) (h : Path k s s) : NeverEnds s := by
  intro j
  apply path_prefix_live (loop_repeat h (j+1))
  nlinarith

def weave {α : Type*} : List α → List α → List α
  | x::xs,y::ys => x::y::weave xs ys
  | _,_ => []
lemma weave_append {α : Type*} (a b c d : List α) (h : a.length=c.length) :
    weave (a++b) (c++d)=weave a c++weave b d := by
  induction a generalizing c with
  | nil => have hc : c=[] := List.length_eq_zero_iff.mp h.symm; subst c; rfl
  | cons x xs ih =>
    cases c with
    | nil => simp at h
    | cons y ys => simp only [List.cons_append,weave,List.length_cons] at *; rw [ih _ (by omega)]
lemma duel_right {α : Type*} [LT α] (a b p q : List α) (h : List.Forall₂ (·<·) a b) :
    Path a.length (a++p,b++q) (p,q++weave a b) := by
  induction h generalizing p q with
  | nil => simpa [weave] using Path.zero (p,q)
  | @cons x y xs ys hxy hrest ih =>
    have hp := ih p (q++[x,y])
    apply Path.cons (Turn.right hxy)
    simpa [weave,List.append_assoc] using hp

def block : ℕ → ℤ → List ℤ
  | 0,v => [v]
  | k+1,v => block k (v-1)++block k v
lemma block_length (k : ℕ) (v : ℤ) : (block k v).length=2^k := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih => simp [block,ih,pow_succ];omega
lemma block_lt (k : ℕ) (v : ℤ) : List.Forall₂ (·<·) (block k v) (block k (v+1)) := by
  induction k generalizing v with
  | zero => exact List.Forall₂.cons (by omega) (List.Forall₂.nil)
  | succ k ih =>
    have h1 := ih (v-1)
    have h2 := ih v
    simpa only [block,show v+1-1=v by omega,sub_add_cancel] using List.rel_append h1 h2
lemma block_weave (k : ℕ) (v : ℤ) :
    weave (block k v) (block k (v+1))=block k v++block k (v+1) := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih =>
    simp only [block]
    rw [weave_append _ _ _ _ (by simp [block_length])]
    have hv : v+1-1=v := by omega
    rw [hv]
    have h1 := ih (v-1)
    simp only [sub_add_cancel] at h1
    rw [h1,ih v]

def copies {α : Type*} : ℕ → List α → List α
  | 0,_ => []
  | a+1,w => w++copies a w
lemma copies_append {α : Type*} (a : ℕ) (w : List α) : copies a w++w=w++copies a w := by
  induction a with
  | zero => simp [copies]
  | succ a ih => simpa only [copies,List.append_assoc] using congrArg (w++·) ih
lemma copies_length {α : Type*} (a : ℕ) (w : List α) : (copies a w).length=a*w.length := by
  induction a with
  | zero => simp [copies]
  | succ a ih => simp [copies,ih,Nat.succ_mul,Nat.add_comm]

def labelStart (a k : ℕ) : State ℤ :=
  (copies (a+1) (block k 1++block k 2),block k 2)
lemma label_loop (a k : ℕ) : Path (2^k+2^k) (labelStart a k) (labelStart a k) := by
  let low := block k 1
  let high := block k 2
  let tail := copies a (low++high)
  have hl : List.Forall₂ (·<·) low high := block_lt k 1
  have hw : weave low high=low++high := block_weave k 1
  have h1 := duel_right low high (high++tail) [] hl
  have h2 := path_swap (duel_right low high high tail hl)
  have h1' : Path (2^k) (labelStart a k) (high++tail,low++high) := by
    simpa [labelStart,copies,low,high,tail,block_length,hw,List.append_assoc] using h1
  have h2' : Path (2^k) (high++tail,low++high) (labelStart a k) := by
    simpa [labelStart,copies,low,high,tail,block_length,hw,copies_append,List.append_assoc] using h2
  exact path_trans h1' h2'
lemma label_neverEnds (a k : ℕ) : NeverEnds (labelStart a k) :=
  neverEnds_of_loop (by have := pow_pos (by decide : 0<(2:ℕ)) k;omega) (label_loop a k)
#print axioms label_loop
def mapState {α β : Type*} (f : α → β) (s : State α) : State β := (s.1.map f,s.2.map f)

lemma turn_lift {α : Type*} [LinearOrder α] (f : α → ℤ) (hf : Monotone f)
    (s : State α) {t : State ℤ} (h : Turn (mapState f s) t) :
    ∃ u, Turn s u ∧ mapState f u=t := by
  rcases s with ⟨p,q⟩
  cases p with
  | nil => cases h
  | cons x xs =>
    cases q with
    | nil => cases h
    | cons y ys =>
      cases h with
      | left hxy =>
        have hyx : y< x := lt_of_not_ge (fun h => (not_lt_of_ge (hf h)) hxy)
        exact ⟨_,Turn.left hyx,by simp [mapState]⟩
      | right hxy =>
        have hxy' : x< y := lt_of_not_ge (fun h => (not_lt_of_ge (hf h)) hxy)
        exact ⟨_,Turn.right hxy',by simp [mapState]⟩

lemma path_lift {α : Type*} [LinearOrder α] (f : α → ℤ) (hf : Monotone f)
    {k : ℕ} {s t : State ℤ} (h : Path k s t) (p : State α) (hp : mapState f p=s) :
    ∃ q, Path k p q ∧ mapState f q=t := by
  induction h generalizing p with
  | zero s => exact ⟨p,Path.zero p,hp⟩
  | @cons k s t u ht hpath ih =>
    have ht' : Turn (mapState f p) t := by rw [hp];exact ht
    obtain ⟨q,hq,hmap⟩ := turn_lift f hf p ht'
    obtain ⟨r,hr,hend⟩ := ih q hmap
    exact ⟨r,Path.cons hq hr,hend⟩

lemma neverEnds_lift_prefix_loop {α : Type*} [LinearOrder α]
    (f : α → ℤ) (hf : Monotone f) {d k : ℕ} {s t : State ℤ}
    (hpre : Path d s t) (loop : Path k t t) (hk : 0< k)
    (p : State α) (hp : mapState f p=s) : NeverEnds p := by
  intro j
  obtain ⟨q,hq,_⟩ := path_lift f hf (path_trans hpre (loop_repeat loop (j+1))) p hp
  exact path_prefix_live hq (by nlinarith)

@[ext] structure Tag (L : List ℤ) where
  index : Fin L.length

def tagEquiv (L : List ℤ) : Tag L ≃ Fin L.length :=
  ⟨Tag.index,Tag.mk,by intro t;cases t;rfl,by intro i;rfl⟩
instance (L : List ℤ) : Fintype (Tag L) := Fintype.ofEquiv (Fin L.length) (tagEquiv L).symm

def tagScore (L : List ℤ) (t : Tag L) : ℤ ×ₗ ℕ := toLex (L[t.index.val],t.index.val)
lemma tagScore_injective (L : List ℤ) : Function.Injective (tagScore L) := by
  intro a b h
  apply Tag.ext
  apply Fin.ext
  exact congrArg (fun z : ℤ ×ₗ ℕ => (ofLex z).2) h
instance (L : List ℤ) : LinearOrder (Tag L) := LinearOrder.lift' (tagScore L) (tagScore_injective L)

def tagLabel (L : List ℤ) (t : Tag L) : ℤ := L[t.index.val]
lemma tagLabel_monotone (L : List ℤ) : Monotone (tagLabel L) := by
  intro a b h
  exact Prod.Lex.monotone_fst (tagScore L a) (tagScore L b) h

/-- Réalisation ordonnée de n occurrences d'étiquettes par n cartes distinctes. -/
lemma realize (s : State ℤ) :
    ∃ (p : State (Fin (s.1++s.2).length)) (f : Fin (s.1++s.2).length → ℤ),
      Monotone f ∧ mapState f p=s ∧
      (p.1++p.2).Perm (List.finRange (s.1++s.2).length) := by
  let L := s.1++s.2
  let e : Fin L.length ≃o Tag L := Fintype.orderIsoFinOfCardEq (Tag L)
    (by simpa using Fintype.card_congr (tagEquiv L))
  let sigma : Equiv.Perm (Fin L.length) := (tagEquiv L).symm.trans e.symm.toEquiv
  let f : Fin L.length → ℤ := fun i => tagLabel L (e i)
  let cards := (List.finRange L.length).map sigma
  have hm : cards.map f=L := by
    rw [List.map_map]
    have he : f ∘ sigma = fun i : Fin L.length => L[i.val] := by
      funext i
      change tagLabel L (e (e.symm (Tag.mk i)))=L[i.val]
      rw [e.apply_symm_apply]
      rfl
    rw [he,← List.ofFn_eq_map]
    exact List.ofFn_getElem
  refine ⟨(cards.take s.1.length,cards.drop s.1.length),f,?_,?_,?_⟩
  · exact (tagLabel_monotone L).comp e.monotone
  · apply Prod.ext
    · change (cards.take s.1.length).map f=s.1
      rw [List.map_take,hm]
      simp [L]
    · change (cards.drop s.1.length).map f=s.2
      rw [List.map_drop,hm]
      simp [L]
  · rw [List.take_append_drop]
    exact sigma.map_finRange_perm

#print axioms realize

lemma weave_length {α : Type*} {R : α → α → Prop} {a b : List α}
    (h : List.Forall₂ R a b) : (weave a b).length=2*a.length := by
  induction h with
  | nil => rfl
  | cons h hp ih => simp [weave,ih];omega

lemma copies_rel (r : ℕ) {a b : List ℤ} (h : List.Forall₂ (·<·) a b) :
    List.Forall₂ (·<·) (copies r a) (copies r b) := by
  induction r with
  | zero => exact List.Forall₂.nil
  | succ r ih => exact List.rel_append h ih

lemma weave_copies {α : Type*} (r : ℕ) (a b : List α) (h : a.length=b.length) :
    weave (copies r a) (copies r b)=copies r (weave a b) := by
  induction r with
  | zero => rfl
  | succ r ih => simp only [copies];rw [weave_append _ _ _ _ h,ih]

/-- Rembobinage simultané d'un suffixe de paires : le gagnant de chaque paire
est remonté dans le premier paquet, le perdant dans le second. -/
lemma balance_weave (a b q : List ℤ) (h : List.Forall₂ (·<·) a b)
    (hsize : q.length ≤ 2*a.length) :
    let n := 2*a.length+q.length
    ∃ (s : State ℤ) (d : ℕ), Path d s (weave a b,q) ∧
      s.1.length=(n+1)/2 ∧ s.2.length=n/2 := by
  intro n
  let c := (n+1)/2
  let d := 2*a.length-c
  let p := a.length-d
  have hlen := h.length_eq
  have hcn : a.length ≤ c ∧ c ≤ 2*a.length := by dsimp [c,n];omega
  have hd : d ≤ a.length := by dsimp [d];omega
  have hp : p ≤ a.length := by dsimp [p];omega
  have hpb : p ≤ b.length := by omega
  let front := weave (a.take p) (b.take p)
  have ht := List.forall₂_take p h
  have hdrop := List.forall₂_drop p h
  have hfront : front.length=2*p := by
    rw [weave_length ht]
    simp [List.length_take,Nat.min_eq_left hp]
  have hdecomp : weave a b=front++weave (a.drop p) (b.drop p) := by
    have hh := weave_append (a.take p) (a.drop p) (b.take p) (b.drop p)
      (by simp [List.length_take,hlen])
    simpa only [List.take_append_drop] using hh
  have hpath := path_swap (duel_right (a.drop p) (b.drop p) q front hdrop)
  refine ⟨(b.drop p++front,a.drop p++q),d,?_,?_,?_⟩
  · have hpd : (a.drop p).length=d := by simp only [List.length_drop];dsimp [p];omega
    rw [hpd] at hpath
    simpa only [Prod.swap_prod_mk,← hdecomp] using hpath
  · simp only [List.length_append,List.length_drop,hfront]
    dsimp [p,d,c,n] at *
    omega
  · simp only [List.length_append,List.length_drop]
    dsimp [p,d,c,n] at *
    omega

lemma labelStart_length (a k : ℕ) :
    ((labelStart a k).1++(labelStart a k).2).length=(2*a+3)*2^k := by
  simp only [labelStart,List.length_append,copies_length,block_length]
  ring

lemma balanced_label_prefix (a k : ℕ) :
    let n := (2*a+3)*2^k
    ∃ (s : State ℤ) (d : ℕ), Path d s (labelStart a k) ∧
      s.1.length=(n+1)/2 ∧ s.2.length=n/2 := by
  intro n
  let A := copies (a+1) (block k 1)
  let B := copies (a+1) (block k 2)
  have hrel : List.Forall₂ (·<·) A B := copies_rel (a+1) (block_lt k 1)
  have hstart : labelStart a k=(weave A B,block k 2) := by
    dsimp [labelStart,A,B]
    rw [weave_copies _ _ _ (by simp [block_length])]
    have hb : weave (block k 1) (block k 2)=block k 1++block k 2 := by simpa using block_weave k 1
    rw [hb]
  have hlen : A.length=(a+1)*2^k := by simp [A,copies_length,block_length]
  have hs : (block k 2).length ≤ 2*A.length := by
    rw [hlen,block_length]
    nlinarith [pow_pos (by decide : 0<(2:ℕ)) k]
  obtain ⟨s,d,hpath,hp,hq⟩ := balance_weave A B (block k 2) hrel hs
  have he : 2*A.length+(block k 2).length=n := by rw [hlen,block_length];dsimp [n];ring
  refine ⟨s,d,?_,?_,?_⟩
  · rwa [← hstart] at hpath
  · simpa only [he] using hp
  · simpa only [he] using hq

lemma decompose_non_power_two {n : ℕ} (hn : 0< n) (hnot : ¬∃k:ℕ,n=2^k) :
    ∃ a k : ℕ, n=(2*a+3)*2^k := by
  obtain ⟨k,m,hm,hnm⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : n≠0)
  obtain ⟨b,hb⟩ := hm
  have hbpos : 0< b := by
    by_contra h
    have hb0 : b=0 := by omega
    have hm1 : m=1 := by omega
    apply hnot
    exact ⟨k,by simpa only [hm1,mul_one] using hnm⟩
  refine ⟨b-1,k,?_⟩
  have he : m=2*(b-1)+3 := by omega
  rw [he] at hnm
  simpa only [mul_comm] using hnm

/-- Énoncé complet sur n cartes distinctes (rang affiché = i.val+1). -/
theorem easy_direction_fin (n : ℕ) (hn : 0< n) (hnot : ¬∃k:ℕ,n=2^k) :
    ∃ s : State (Fin n), (s.1++s.2).Perm (List.finRange n) ∧
      s.1.length=(n+1)/2 ∧ s.2.length=n/2 ∧ NeverEnds s := by
  obtain ⟨a,k,hnum⟩ := decompose_non_power_two hn hnot
  obtain ⟨pre,d,hpre,hp,hq⟩ := balanced_label_prefix a k
  have hp' : pre.1.length=(n+1)/2 := by simpa only [← hnum] using hp
  have hq' : pre.2.length=n/2 := by simpa only [← hnum] using hq
  have hlen : (pre.1++pre.2).length=n := by rw [List.length_append,hp',hq'];omega
  obtain ⟨s,f,hmono,hmap,hperm⟩ := realize pre
  have hpl : s.1.length=pre.1.length := by
    have hh := congrArg (fun p => p.1.length) hmap
    simpa [mapState] using hh
  have hql : s.2.length=pre.2.length := by
    have hh := congrArg (fun p => p.2.length) hmap
    simpa [mapState] using hh
  have hne : NeverEnds s := neverEnds_lift_prefix_loop f hmono hpre (label_loop a k)
    (by have hh := pow_pos (by decide : 0<(2:ℕ)) k;omega) s hmap
  cases hlen
  exact ⟨s,hperm,hpl.trans hp',hql.trans hq',hne⟩

#print axioms easy_direction_fin

lemma mapState_step {α β : Type*} [LinearOrder α] [LinearOrder β]
    (f : α → β) (hf : StrictMono f) (s : State α) :
    mapState f (step s)=step (mapState f s) := by
  rcases s with ⟨p,q⟩
  cases p <;> cases q <;> simp [mapState,step,hf.lt_iff_lt]
  split_ifs <;> simp

lemma mapState_run {α β : Type*} [LinearOrder α] [LinearOrder β]
    (f : α → β) (hf : StrictMono f) (k : ℕ) (s : State α) :
    mapState f (run k s)=run k (mapState f s) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    change mapState f (run k (step s))=run k (step (mapState f s))
    rw [ih,mapState_step f hf]

lemma mapState_neverEnds {α β : Type*} [LinearOrder α] [LinearOrder β]
    (f : α → β) (hf : StrictMono f) {s : State α} (hs : NeverEnds s) :
    NeverEnds (mapState f s) := by
  intro k
  rw [← mapState_run f hf]
  simpa only [mapState,live,ne_eq,List.map_eq_nil_iff] using hs k

lemma map_finRange_succ (n : ℕ) :
    (List.finRange n).map (fun i => i.val+1)=List.range' 1 n := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [Nat.add_comm]

/-- Sens facile complet : donne équilibrée des cartes distinctes 1,...,n,
avec retour perdante d'abord, gagnante ensuite, et partie jamais terminée. -/
theorem easy_direction (n : ℕ) (hn : 0< n) (hnot : ¬∃k:ℕ,n=2^k) :
    ∃ s : State ℕ, (s.1++s.2).Perm (List.range' 1 n) ∧
      s.1.length=(n+1)/2 ∧ s.2.length=n/2 ∧ NeverEnds s := by
  obtain ⟨s,hperm,hp,hq,hne⟩ := easy_direction_fin n hn hnot
  let f : Fin n → ℕ := fun i => i.val+1
  have hf : StrictMono f := by intro a b hab;change a.val+1< b.val+1;exact Nat.add_lt_add_right hab 1
  refine ⟨mapState f s,?_,?_,?_,mapState_neverEnds f hf hne⟩
  · have hh := hperm.map f
    simpa only [mapState,← List.map_append,f,map_finRange_succ] using hh
  · simpa only [mapState,List.length_map] using hp
  · simpa only [mapState,List.length_map] using hq

#print axioms easy_direction

example : run 2 (([1,3],[2]) : State ℕ)=([1,3],[2]) := by decide

#eval run 2 (([1,3],[2]) : State ℕ)
end A400868
