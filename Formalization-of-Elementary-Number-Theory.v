Require Export ssrfun ssrbool ssreflect Utf8_core Setoid List
  SetoidPermutation SetoidList Ring Sorted Constructive_sets Wf_nat
  ProofIrrelevance Permutation ClassicalDescription ChoiceFacts.
(** Math symbols for cut and paste: ∀ ∃ → ↔ ∧ ∨ ¬ ≠ ≤ ≥ ∅ ℕ ℤ ∈ ∉ ⊂ ∑ ∏ λ **)

Module Type Z_Axioms.

  Parameter Z : Set.

  Parameter add mul : Z → Z → Z.
  Parameter neg : Z → Z.
  Parameter zero one : Z.
  Notation "0" := zero.
  Notation "1" := one.
  Infix "+" := add.
  Infix "*" := mul.
  Notation "- x" := (neg x).
  Notation "- 0" := (neg 0).
  Notation "- 1" := (neg 1).

  Axiom add_comm   : ∀ a b   : Z, a + b = b + a.
  Axiom add_assoc  : ∀ a b c : Z, a + (b + c) = (a + b) + c.
  Axiom add_0_l    : ∀ a     : Z, 0 + a = a.
  Axiom add_inv_r  : ∀ a     : Z, a + -a = 0.
  Axiom mul_comm   : ∀ a b   : Z, a * b = b * a.
  Axiom mul_assoc  : ∀ a b c : Z, a * (b * c) = (a * b) * c.
  Axiom mul_1_l    : ∀ a     : Z, 1 * a = a.
  Axiom mul_distr_r : ∀ a b c : Z, (a + b) * c = a * c + b * c.
  Axiom ord_nontrivial: ∃ x : Z, x ≠ 0.
  Axiom ord : Z → Z → Prop.
  Infix "<" := ord.
  Notation " a > b" := (b < a) (only parsing).
  Axiom trich_exclusive : ∀ a b : Z,(a = b ∧ ¬ a < b ∧ ¬ b < a)
                                  ∨ (¬ a = b ∧ a < b ∧ ¬ b < a)
                                  ∨ (¬ a = b ∧ ¬ a < b ∧ b < a).
  (* transitive needed to prevent weak ordering.*)
  Axiom ord_trans   : ∀ x y z, x < y → y < z → x < z.
  Axiom trichotomy  : ∀ a b : Z, a = b ∨ a < b ∨ b < a.
  Axiom ord_add     : ∀ x y z, x < y → x + z < y + z.
  Axiom ord_mul     : ∀ x y z, 0 < z → x < y → x * z < y * z.

  Definition le : Z → Z → Prop. 
    Proof.
    intros a b.
    exact (a < b ∨ a = b).
  Defined.
  Infix "≤" := le (at level 70, no associativity).
  Notation "a ≥ b" := (b ≤ a) (at level 70, no associativity, only parsing).
  Notation "a < b < c" := (a < b ∧ b < c).
  Notation "a ≤ b < c" := (a ≤ b ∧ b < c) (at level 70, b at next level).
  Notation "a < b ≤ c" := (a < b ∧ b ≤ c) (at level 70, b at next level).
  Notation "a ≤ b ≤ c" := (a ≤ b ∧ b ≤ c) (at level 70, b at next level).
  Infix "∋" := (In Z) (at level 70).
  Notation "a ∈ S" := (S ∋ a) (at level 70).
  Definition bounded_below (S : Ensemble Z) :=
    ∃ m : Z, ∀ s : Z, s ∈ S → m < s.
  Axiom WOP : ∀ S : Ensemble Z, S ≠ (Empty_set Z) →
    bounded_below S → ∃ s : Z, s ∈ S ∧ (∀ m : Z, m ∈ S → ¬ m < s).

  Inductive positive : (Ensemble Z) :=
  | one_pos : positive 1
  | add_pos : ∀ a, positive a → positive (a + 1).

End Z_Axioms.

Module Z_Theory (Z : Z_Axioms).

  Export Z.

  Definition sub a b := a + -b.
  Infix "-" := sub.

  Add Ring Z_ring :
	(mk_rt _ _ _ _ _ _ _ add_0_l add_comm add_assoc mul_1_l mul_comm
	   mul_assoc mul_distr_r (λ _ _, erefl) add_inv_r).

Theorem trichotomy: ∀ a b : Z, a = b ∨ a < b ∨ b < a.
  intros. 
  destruct (trich_exclusive a b) as [H |[ H | H ]].
  tauto. tauto. tauto.
Qed.
Theorem ord_irrefl:  ∀ a : Z, ¬ (a < a).
  intro. destruct (trich_exclusive a a) as [H |[ H | H ]].
  tauto. exfalso. assert (a=a) by reflexivity. tauto. tauto.
Qed.
Theorem ord_antisym : ∀ a b, a < b → ¬ (b < a).
    intros ????.
    destruct (trich_exclusive a b) as [H1 | [ H1 | H1 ] ].
    apply (ord_irrefl a). tauto. tauto. tauto.
Qed.
Definition abs: Z → Z.
  Proof.
  intros x.
  pose proof (trichotomy 0 x) as H.
  destruct (excluded_middle_informative (0 < x)).
    - exact x.
    - exact (-x).
Defined.
Definition divide (x y : Z) := ∃ z : Z, y = z * x.
  Notation "( x | y )" := (divide x y).
Definition unit (x : Z) := (divide x 1).
(* Relatively prime *)
Definition rel_prime (a b : Z) := ∀ d : Z, (d | a) → (d | b) → unit d.

Definition prime (p : Z) := p ≠ 0 
∧ ¬ unit p 
∧ ∀ a b : Z, (p | a * b) → (p | a) ∨ (p | b).

Definition assoc (a b : Z) := (a | b) ∧ (b | a).
Definition pm (a b : Z) := (a = b ∨ a = -b).
Notation "a = ± b" := (pm a b) (at level 70).
Infix "~" := assoc (at level 70).

Definition irreducible (p : Z) := ¬ unit p ∧ ∀ d : Z, (d | p) → unit d ∨ d ~ p.
Theorem Contrapositive : ∀ P Q : Prop, (P → Q) ↔ (¬ Q → ¬ P).
  split. intros. eauto. intros. apply NNPP. tauto.
Qed. 

Theorem A1P1 : ∀ a : Z, a + 0 = a.
  Proof. intros. ring.
Qed. (* replace "Admitted." with "Qed." when your proof is finished. *)
Theorem A1P2 : ∀ a : Z, -a + a = 0.
  Proof. intros. ring.
Qed. (* replace "Admitted." with "Qed." when your proof is finished. *)
Theorem A1P3 : ∀ a : Z, a * 1 = a.
  Proof. intros a. ring.
Qed. (* replace "Admitted." with "Qed." when your proof is finished. *)
Theorem A1P4 : ∀ a : Z, a - 0 = a.
  Proof. intros.
  assert (a + 0 = a) as H by apply A1P1. rewrite -{1}H.
  unfold sub. rewrite -add_assoc. ring.
Qed. (* replace "Admitted." with "Qed." when your proof is finished. *)
Theorem A1P5 : ∀ a b : Z, a + b = 0 → b = -a.
  Proof.
  intros a b P.
  rewrite add_comm in P.
  apply (f_equal (add^~ (-a))) in P.
  rewrite -add_assoc add_inv_r A1P1 add_0_l in P; exact.
Qed. (* replace "Admitted." with "Qed." when your proof is finished. *)
Theorem A1P6 : ∀ a : Z, -(-a) = a.
  Proof.
  intros a.
  assert (-a + a = 0) as H by apply A1P2.
  apply A1P5 in H; symmetry; exact.
Qed. (* replace "Admitted." with "Qed." when your proof is finished. *)
Theorem A1P7 : ∀ a : Z, 0 * a = 0.
  Proof.
	intros.
	assert (0 +0 = 0) as H. by rewrite add_0_l; reflexivity.
	apply (f_equal (mul^~ a)) in H.
	rewrite mul_distr_r in H.
	apply (f_equal (add^~ (- (0 * a)))) in H.
	rewrite add_inv_r -add_assoc add_inv_r A1P1 in H; ring.
Qed. (* replace "Admitted." with "Qed." when your proof is finished. *)
Lemma minus_0_eq_0 : -0 = 0.
  Proof.
  assert (-0 + 0 = 0) as H by apply (A1P2 0).
  rewrite add_comm add_0_l in H. exact.
  Qed.

Theorem A1P8 : ∀ a : Z, -1 * a = -a.
  Proof.
  intros.
  assert (1 + -1 = 0) as H by apply add_inv_r.
  apply (f_equal (mul^~ a)) in H.
  rewrite A1P7 mul_distr_r mul_1_l in H.
  apply A1P5 in H; exact H.
Qed. (* replace "Admitted." with "Qed." when your proof is finished. *)
Lemma mul_neg_comm : ∀ a b : Z, -a * b = a * -b.
  intros ??.
  rewrite -A1P8 -(A1P8 b) mul_assoc (mul_comm a (-1)). trivial.
Qed.
Theorem add_neg_dist : ∀ a b : Z, -( a + b ) = - a + - b.
  intros.
  ring.
Qed.
Theorem mul_neg_dist : ∀ a b : Z, -( a * b ) = a * - b.
  intros.
  ring.
Qed.
Theorem neg_refl: ∀ a b : Z, -a = b → a = -b.
  intros. rewrite -H A1P6. reflexivity.
Qed.
Theorem A1P9 : ∀ a b : Z, -a * -b = a * b.
  Proof.
  intros. ring.
Qed.
    
Theorem A1P10 : ∀ a b : Z, a + b = a → b = 0.
  Proof.
  intros a b H.
  apply (f_equal (add^~ (-a))) in H.
  rewrite -add_assoc (add_comm b) add_assoc add_inv_r add_0_l in H.
  exact H.
Qed. (* replace "Admitted." with "Qed." when your proof is finished. *)

(*For P11 and P12, we establish orderings to zoom into Z instead of a general
 commutative ring. Define an operation < with following properties:*)

Lemma ord_neq : ∀ a b, a < b → a ≠ b.
    intros a b Hab Heq; subst.
    apply (ord_antisym b b Hab Hab).
Qed.

Lemma ord_neg : ∀ x y : Z, x < y → -y < -x.
    Proof.
    intros.
    apply (ord_add x y (-x)) in H.
    rewrite add_inv_r in H.
    apply (ord_add 0 (y+-x) (-y)) in H.
    rewrite (add_comm y (-x)) -add_assoc add_inv_r (add_comm (-x) 0) add_0_l add_0_l in H.
    exact H.
  Qed.
Lemma ord_neg0     : ∀ x, 0 < x → -x < 0.
    Proof.
    intros x Hx.
    apply (ord_add 0 x (-x)) in Hx.
    rewrite add_inv_r add_0_l in Hx.
    exact Hx.
  Qed.
Lemma ord_nneg     : ∀ x, x < 0 → 0 < -x.
  Proof.
  intros x Hx.
  pose proof (ord_neg x 0 Hx). rewrite -minus_0_eq_0. exact.
  Qed.
Lemma ord_mul_n0 : ∀ x y , 0 < x → y < 0 → x * y < 0.
  Proof.
  intros.
  assert (0 < -y).
  {apply (ord_neg y 0) in H0; rewrite -minus_0_eq_0. assumption. }
  pose proof (ord_mul 0 (-y) x H H1).
  rewrite A1P7  -A1P8 in H2.
  apply ord_neg0 in H2.
  rewrite -A1P8 mul_assoc mul_assoc A1P9 mul_1_l mul_1_l mul_comm in H2.
  exact H2.
  Qed.

Lemma ord_mul_nn00 : ∀ x y, x < 0 → y < 0 → 0 < x * y.
    intros x y Hx Hy.
    apply ord_nneg in Hx.
    apply ord_nneg in Hy.
    apply (ord_mul 0 (-x) (-y)) in Hx; try assumption.
    rewrite A1P7 A1P9 in Hx. easy.
  Qed.
Lemma ord_mul_neg : ∀ x y z, x < 0 → y < z → x * z < x * y.
    intros.
    apply ord_neg in H.
    rewrite minus_0_eq_0 in H.
    pose proof (ord_mul y z (-x) H H0) as H1.
    apply (ord_add (y * - x) (z * - x) (y*x)) in H1.
    rewrite mul_comm (mul_comm y x) -mul_distr_r (add_comm (-x) x) add_inv_r A1P7 in H1.
    apply (ord_add 0 (z * - x + x * y) (z*x)) in H1.
    rewrite (mul_comm z (-x)) (mul_comm z x) (add_comm (- x * z)(x * y)) -add_assoc -(mul_distr_r (-x) x z) (add_comm (-x) x) add_inv_r A1P7 in H1.
    rewrite add_0_l add_comm add_0_l in H1. trivial.
Qed.


Theorem abs_pm : ∀ a, (abs a = a) ∨ (abs a = -a).
  intros; unfold abs; destruct excluded_middle_informative; auto.
  Qed.
Theorem A1P12 : ∀ a b : Z, a * b = 0 → a = 0 ∨ b = 0.
  Proof.
  intros a b H.
  assert (0=0) as Hzero by reflexivity.
  destruct (trichotomy 0 a) as [H0 | [Hpos | Hneg]].
    - symmetry in H0. left; exact H0.
    - destruct (trichotomy 0 b) as [Hb0 | [Hbpos | Hbneg]]. (* 0 < a *)
      + symmetry in Hb0. right; exact Hb0.
      + apply (ord_mul 0 b a) in Hpos; try assumption.
        rewrite A1P7 mul_comm in Hpos.
        pose proof (ord_neq 0 (a*b) Hpos) as Hneq.
        rewrite H in Hneq.
        contradiction Hzero.
      + apply (ord_mul_n0 a b) in Hbneg; try assumption.
        pose proof (ord_neq (a*b) 0 Hbneg) as Hneq. (*similar for b<0.*)
        rewrite H in Hneq.
        contradiction Hzero.
    - destruct (trichotomy 0 b) as [Hb0 | [Hbpos | Hbneg]]. (* a < 0 3 cases *)
      + symmetry in Hb0. right. exact Hb0.
      + apply (ord_mul a 0 b) in Hbpos; try assumption.
        rewrite A1P7 in Hbpos.
        pose proof (ord_neq (a*b) 0 Hbpos) as Hneq; rewrite H in Hneq.
        contradiction.
      + apply (ord_mul_nn00 a b) in Hneg; try assumption.
        pose proof (ord_neq 0 (a*b) Hneg) as Hneq; rewrite H in Hneq.
        contradiction.
Qed.

Theorem A1P11 : ∀ a b : Z, a * b = a ∧ a ≠ 0 → b = 1.
  Proof.
  intros a b [H1 H2].
  apply (f_equal (add^~ (neg a))) in H1.
  rewrite -{1}A1P8 (mul_comm a) -mul_distr_r (add_inv_r a) in H1.
  apply A1P12 in H1.
  destruct H1 as [H1|H1]; try assumption.
  rewrite add_comm in H1.
  apply A1P5 in H1. 
  rewrite A1P6 in H1. 
  exact. contradiction.
Qed. 


Theorem A2P1 : ∀ a m n x y : Z, (a | m) → (a | n) → (a | m * x + n * y).
  Proof.
  intros.
  destruct H as [i Hi].
	destruct H0 as [j Hj].
	rewrite mul_comm (mul_comm n) Hi Hj mul_assoc mul_assoc -mul_distr_r.
	exists (x * i + y * j); easy. 
Qed.
	
Theorem A2P2: ∀ a b c : Z, (a | b) → (b | c) → (a | c).
  Proof.
	intros.
	destruct H as [i Hi].
	destruct H0 as [j Hj].
	rewrite Hi mul_assoc in Hj.
	exists (j * i); easy.
Qed.

(*A2P3, A2P4, A2P5 collaborated with Erika Shan*)
(*relatively natural to establish order as real integers*)
Theorem A2P3 : 0 ≠ 1.
  Proof.
  intro. pose proof ord_nontrivial as Hx.
  destruct Hx as [x Hx].
  apply (f_equal (mul^~ x)) in H; rewrite mul_1_l A1P7 in H.
  rewrite H in Hx.
  contradiction.
Qed.

(*units in Z should contain ±1. *)
(*Since 0≠1,  0 < 1. order established.*)
Lemma z_lt_1 : 0 < 1.
  Proof.
  destruct (trichotomy 0 1) as [Heq | [H01 | H10]].
  - exfalso. apply A2P3 in Heq. exact Heq.
  - exact H01.
  - destruct ord_nontrivial as [x Hx].
    destruct (trichotomy 0 x) as [Hx0 | [Hxpos | Hxneg]].
    + exfalso. rewrite Hx0 in Hx. contradiction.
    + pose proof (ord_mul 1 0 x Hxpos H10) as Hcontra1.
      rewrite mul_1_l A1P7 in Hcontra1.
      pose proof (ord_antisym 0 x Hxpos) as Hnot.
      exfalso. apply Hnot. exact Hcontra1.
    + pose proof (ord_nneg x Hxneg) as Hpos_negx.
      pose proof (ord_mul 1 0 (- x) Hpos_negx H10) as Hcontra2.
      rewrite mul_1_l A1P7 in Hcontra2.
      pose proof (ord_antisym 0 (- x) Hpos_negx) as Hnot2.
      exfalso. apply Hnot2. exact Hcontra2.
  Qed.
Lemma n1_lt_0 : -1 < 0.
  pose proof z_lt_1. apply ord_neg0 in H. exact.
  Qed.
Lemma divide_refl : ∀ a : Z, (a | a).
  intros. exists 1. rewrite mul_1_l. reflexivity.
Qed.
Lemma divide_zero_all : ∀ a : Z, (a | 0).
  intros. exists 0. rewrite A1P7. reflexivity.
Qed.
Lemma one_divides_all : ∀ a : Z, (1 | a).
  intros; exists a; ring.
  Qed.
Lemma divide_neg : ∀ a b : Z, ( a | b ) → ( a | -b ).
  intros. destruct H. exists (-1*x). rewrite -mul_assoc -H A1P8. exact.
Qed.
Lemma ord_mul_rev : ∀ x y : Z , x > 0 → x * y > 0 → y > 0.
  Proof.
  intros x y Hx Hxy.
  destruct (trichotomy 0 y) as [Heq | [Hpos | Hneg]]; try exact.
    - exfalso.
      rewrite -Heq mul_comm A1P7 in Hxy.
      apply ord_irrefl in Hxy; exact.
    - exfalso.
      apply (ord_mul_n0 x y) in Hneg; try assumption.
      apply ord_antisym in Hneg; contradiction.
  Qed.
Lemma ord_1_rev : ∀ x y : Z , x > 1 → x * y = 1 → y < 1.
  intros.
  destruct (trichotomy 1 y) as [Heq | [Hpos | Hneg]]; try exact.
    - rewrite -Heq mul_comm mul_1_l in H0.
      pose proof (ord_neq 1 x H) as Hneq.
      symmetry in H0.
      contradiction Hneq.
    - exfalso.
      pose proof z_lt_1.
      assert (0 < x) as Hx. by apply (ord_trans 0 1 x); exact. 
      apply (ord_mul 1 y x) in Hx.
      rewrite mul_1_l in Hx.
      apply (ord_trans 1 x (y*x)), ord_neq in Hx.
      rewrite mul_comm in H0.
      symmetry in H0.
      contradiction Hx.
      exact H. exact Hpos.
  Qed.

(* To separate ℤ from ℚ and ℝ, we must ensure that 1 is the minimum 
distance, or nothing exists between. *)
Lemma  dne_in_01 : ∀ z : Z, ¬(0 < z ∧ z < 1).
  intros z [Hz0 Hz1].
  set (S := fun z => 0 < z ∧ z < 1).
  assert (S_nonempty : S z) by (split; assumption).
  assert (S_not_empty : S ≠ Empty_set Z).
    {intros H; rewrite H in S_nonempty; inversion S_nonempty. }
  assert (S_bounded : bounded_below S).
    {exists 0; intros s [Hs0 Hs1]; exact Hs0. }
  destruct (WOP S S_not_empty S_bounded) as [s [[Hs0 Hs1] Hmin]].
  assert (Hss0 : 0 < s*s).
    apply (ord_mul 0 s s) in Hs0 as H. rewrite A1P7 in H; auto. auto.
  assert (Hss : s*s < s).
    apply (ord_mul s 1 s) in Hs1 as H. rewrite mul_1_l in H. auto. auto.
  assert (s*s ∈ S). split; auto.
    - apply (ord_trans (s*s) s 1 Hss Hs1).
    - specialize (Hmin (s*s) H); contradiction.
  Qed.
Lemma dne_nonint : ∀ x i : Z, ¬(i < x ∧ x < i + 1).
  Proof.
  intros x i [Hi_x Hx_succ].
  apply (ord_add i x (-i)) in Hi_x.
  apply (ord_add x (i + 1) (-i)) in Hx_succ.
  rewrite -add_assoc (add_comm 1 (-i)) add_assoc add_inv_r add_0_l in Hx_succ.
  rewrite add_inv_r in Hi_x.
  set (y := x + (-i)) in *.
  pose proof (dne_in_01 y).
  apply H. split; assumption.
  Qed.  

(*TOUGH WORK. examines a and i with trichotomy on ±1.*)
Theorem A2P4 : ∀ a : Z, unit a -> a = 1 ∨ a = -1.
  Proof.
  intros a [i Hi].
  destruct (trichotomy a 1) as [Heq | [Hlt | Hgt]]; auto.
  - destruct (trichotomy a (-1)) as [Heq | [Hlt0 | Hgt]]; auto.
    + assert (a < 0) as Halt0.
      {pose proof (ord_trans a (-1) 0 Hlt0 n1_lt_0) as Htrans; exact Htrans. }
      destruct (trichotomy i 0) as [Hi_eq | [Hi_lt | Hi_gt]]; exfalso.
      * rewrite Hi_eq A1P7 in Hi.
        symmetry in Hi.
        pose proof A2P3.
        contradiction.
      * symmetry in Hi.
        rewrite mul_comm in Hi.
        apply ord_neg in Hlt0.
        rewrite A1P6 in Hlt0.
        rewrite -A1P9 in Hi.
        pose proof (ord_1_rev (-a) (-i) Hlt0 Hi) as Hi_lt1.
        apply ord_neg in Hi_lt1.
        rewrite A1P6 in Hi_lt1.
        pose proof (dne_nonint i (-1)) as Hcontra.
        rewrite add_comm add_inv_r in Hcontra.
        assert ((-1) < i ∧ i < 0) as Hand.
        {split; try assumption. } 
        apply Hcontra in Hand; exact.
      * assert (0 > a*i) as Hailt0.
          {pose proof (ord_mul_n0 i a Hi_gt Halt0) as Htrans;
          rewrite mul_comm in Htrans; exact Htrans. }
        symmetry in Hi.
        rewrite mul_comm in Hi.
        pose proof (ord_trans (a*i) 0 1 Hailt0 z_lt_1).
        apply ord_neq in H.
        contradiction.
    + destruct (trichotomy a 0) as [Ha_eq0 | [Ha_lt0 | Ha_gt0]]; exfalso. 
      * rewrite Ha_eq0 mul_comm A1P7 in Hi.
        symmetry in Hi.
        pose proof A2P3.
        contradiction.
      * pose proof (dne_nonint a (-1)).
        rewrite add_comm add_inv_r in H.
        assert (-1 < a ∧ a < 0) as Hand. by split; assumption.
        auto.
      * pose proof (dne_nonint a 0).
        rewrite add_0_l in H.
        assert (0 < a ∧ a < 1) as Hand. by split; try assumption. 
        auto.
  - assert (0 < a) as Hagt0.
      {pose proof (ord_trans 0 1 a z_lt_1 Hgt) as Htrans; exact Htrans. }
    destruct (trichotomy i 0) as [Hi_eq | [Hi_lt | Hi_gt]]; exfalso.
    + rewrite Hi_eq A1P7 in Hi.
      symmetry in Hi.
      pose proof A2P3.
      contradiction.
    + assert (0 < a*i) as Haigt0.
        {pose proof z_lt_1. rewrite Hi in H. rewrite mul_comm in H. exact H. }
      assert (i>0) as Hi_pos.
        {pose proof (ord_mul_rev a i Hagt0 Haigt0) as Higt0. exact Higt0. }
      apply ord_antisym in Hi_lt.
      contradiction.
    + symmetry in Hi.
      rewrite mul_comm in Hi.
      pose proof (ord_1_rev a i Hgt Hi) as Hi_lt1.
      pose proof (dne_nonint i 0) as Hcontra.
      rewrite add_0_l in Hcontra.
      assert (0 < i ∧ i < 1) as Hand. by split; try assumption. 
      auto.
  Qed.
Theorem A2P5 : ∀ a b c : Z, a * c = b * c → c ≠ 0 → a = b.
  Proof.
  intros.
  apply (f_equal (add^~ (-b*c))) in H.
  rewrite -mul_distr_r -mul_distr_r  (add_inv_r b) A1P7 in H.
  apply A1P12 in H.
  destruct H as [H|H].
    - rewrite add_comm in H.
      apply A1P5 in H. 
      rewrite (A1P6 b) in H; exact.
    - exfalso.
      exact (H0 H).
  Qed.

(*original A2P6 may prove false when a is composite. 
define prime to avoid.*)

Theorem A2P6 : ∀ p a b : Z, prime p → ¬ (p | a) → (p | a * b ) → (p | b).
  Proof.
  intros.
  unfold prime in H.
  destruct H as [Hne [Hnu Hpr]].
  destruct (Hpr a b H1) as [Hp_a | Hp_b]; auto. exfalso. exact (H0 Hp_a).
Qed.

Theorem A3P0 : ∀ a b : Z, a < b → a ≤ b.
    intros. unfold le. tauto.
Qed.

Theorem A3P1 : ∀ a b, a < b ∨ a = b ∨ a > b.
  intros. destruct (trichotomy a b) as [Heq | [Hlt | Hgt]];tauto.
Qed.

Theorem A3P2 : ∀ a b : Z, a < b ↔ 0 < b - a.
  Proof.
  intros; split; intros.
  - apply (ord_add a b (-a)) in H.
    rewrite add_inv_r in H; tauto.
  - unfold sub in H.
    apply (ord_add 0 (b + -a) a) in H.
    rewrite -add_assoc (add_comm (-a) a) add_inv_r (add_comm b 0) add_0_l add_0_l in H.
    exact.
Qed.

Theorem A3P3 : 0 < 1.
  exact z_lt_1.
Qed.

Theorem A3P4 : ∀ a, ¬ 0 < a < 1.
  exact dne_in_01.
Qed.

Lemma abs_nonneg : ∀ a : Z, 0 ≤ abs a.
  Proof.
  intros.
  unfold le.
  destruct (trichotomy 0 (abs a)) as [Heq | [Hlt | Hgt]]; auto.
  - exfalso.
    unfold abs in Hgt.
    destruct excluded_middle_informative.
    + apply ord_antisym in Hgt; contradiction.
    + apply ord_neg in Hgt.
      rewrite A1P6 minus_0_eq_0 in Hgt; contradiction.
  Qed.
Lemma abs0 : ∀ a : Z, a = 0 ↔ abs a = 0.
  intros; split.
  unfold abs; destruct excluded_middle_informative; auto.
  intros. rewrite H. apply minus_0_eq_0.
  intros. unfold abs in H; destruct excluded_middle_informative; auto.
  apply (f_equal (add^~ a)) in H. rewrite add_comm add_inv_r add_0_l in H. auto.
  Qed.
Lemma absn0 : ∀ a : Z, a ≠ 0 ↔ abs a > 0.
  intros. pose proof (abs_nonneg a). split. 
  apply Contrapositive. intros.
  destruct H. exfalso. exact. symmetry in H. apply abs0 in H. tauto.
  intros. pose proof (abs0 a). destruct H1. apply Contrapositive in H1. exact.
  intro. apply ord_neq in H0. symmetry in H4. exact.
Qed.
Lemma abs_neg : ∀ a : Z, abs a = abs (-a).
  Proof.
  intros a.
  destruct (trichotomy 0 a) as [Ha0 | [Ha_pos | Ha_neg]].
  - rewrite -Ha0 minus_0_eq_0. trivial.
  - unfold abs. destruct (excluded_middle_informative (0 < a)).
    destruct (excluded_middle_informative); try contradiction.
    exfalso. apply ord_antisym in o0.
    apply ord_neg in o. rewrite minus_0_eq_0 in o. contradiction.
    rewrite A1P6. trivial.
    destruct (excluded_middle_informative); auto. contradiction.
  - unfold abs. destruct (excluded_middle_informative (0 < a)). 
    destruct (excluded_middle_informative); try contradiction.
    exfalso. apply ord_antisym in o0.
    apply ord_neg in o. rewrite minus_0_eq_0 in o; contradiction.
    rewrite A1P6. trivial.
    destruct (excluded_middle_informative). trivial. 
    apply ord_neg in Ha_neg. rewrite minus_0_eq_0 in Ha_neg. contradiction.
  Qed.

(*Lemma abs_mul : ∀ a b : Z,  abs a * abs b = abs (a*b).*)
Lemma A3P51 : ∀ a b k : Z, 1 < k → b = k * a → abs a < abs b ∨ abs a = abs b.
  intros a b k Hkpos Hk.
  destruct (trichotomy 0 a) as [Ha0 | [Hapos | Haneg]].
    + rewrite -Ha0 mul_comm A1P7 in Hk. symmetry in Ha0. 
      apply (abs0 a) in Ha0. apply (abs0 b) in Hk. 
      rewrite Ha0 Hk; auto.
    + apply (ord_mul 1 k a) in Hkpos.
      rewrite mul_1_l -Hk in Hkpos.
      pose proof (ord_trans 0 a b Hapos Hkpos).
      unfold abs; destruct (excluded_middle_informative (0 < a)); try contradiction.
      destruct (excluded_middle_informative (0 < b)); tauto. auto.
    + pose proof (ord_trans 0 1 k A3P3 Hkpos).
      pose proof (ord_mul_neg a 1 k Haneg Hkpos). rewrite (mul_comm a 1) mul_1_l in H0.
      rewrite mul_comm -Hk in H0. 
      pose proof (ord_trans b a 0 H0 Haneg).
      apply ord_antisym in Haneg. apply ord_antisym in H1.
      unfold abs. destruct (excluded_middle_informative). contradiction.
      destruct (excluded_middle_informative). contradiction.
      apply (ord_neg) in H0; tauto.
  Qed.
(*The negatives are discarded in the intial question. Also, if b=0, the 
conclusion is unprovable.*)
Theorem A3P5 : ∀ a b, (a | b) → b ≠ 0 → abs a ≤ abs b.
  Proof.
  intros a b Hdiv Hbn0.
  destruct Hdiv as [k Hk].
  unfold "≤". 
  destruct (trichotomy 1 k) as [Hk1 | [Hkpos | Hkneg1]].
  - rewrite -Hk1 mul_1_l in Hk. rewrite Hk. auto.
  - apply (A3P51 a b k Hkpos Hk).
  - destruct (trichotomy 0 k) as [Hk0 | [Hkpos | Hkneg]].
    + rewrite -Hk0 A1P7 in Hk. contradiction.
    + exfalso. pose proof (dne_in_01 k). tauto.
    + destruct (trichotomy (-1) k) as [Hk0 | [Hapos | Haneg]].
      * rewrite -Hk0 A1P8 in Hk. rewrite Hk. right. exact (abs_neg a).
      * exfalso. pose proof (dne_nonint k (-1)).
        rewrite add_comm add_inv_r in H. tauto.
      * apply ord_neg in Haneg.
        rewrite A1P6 in Haneg.
        rewrite -A1P9 in Hk.
        pose proof (A3P51 (-a) b (-k) Haneg Hk).
        rewrite -abs_neg in H. trivial.
  Qed.
(*Cannot figure out the other way round.*)

Lemma existence : ∀ P : Ensemble Z, (∃ k, P k) → P ≠ Empty_set Z.
  intros ???. inversion H. rewrite H0 in H1. inversion H1.
Qed.
Lemma existence_rev : ∀ P : Ensemble Z, P ≠ Empty_set Z → (∃ k, P k).
  intros.
  destruct (classic (∃ k : Z, P k)) as [Hex | Hneg]; auto.
  exfalso. apply H.
  apply Extensionality_Ensembles; split; intros x Hx.
  exfalso; apply Hneg; exists x; exact Hx. contradiction.
Qed.
(*A3P6 collaborated with Jason Tang*)
Theorem A3P6 : ∀ P : Z → Prop, (∀ n, (∀ k, 0 < k < n → P k) → P n) → ∀ n : Z, P n.
  Proof.
  intros P Hind n.
  set (S := fun k : Z => 0 < k ∧ ~ P k).
  destruct (excluded_middle_informative (exists k, S k)) as [Hex | Hno].
  - destruct Hex as [s Hs].
    assert (S ≠ Empty_set Z) as S_nonempty.
      { intro Heq. rewrite Heq in Hs. inversion Hs. }
    assert (bounded_below S).
      { unfold bounded_below. exists 0. intros t [Htpos]. exact Htpos. }
    destruct (WOP S S_nonempty H) as [m [Hm_min Hm_least]]; auto.
    destruct Hm_min as [Hm_pos Hm_notP].
    assert (Hsmaller: ∀ k : Z, 0 < k < m → P k).
      { intros k Hk.
      destruct (excluded_middle_informative (P k)) as [Hpk | Hnpk]; auto.
      exfalso. apply (Hm_least k).
      split. tauto. tauto. tauto. }
    specialize (Hind m Hsmaller); contradiction.
  - destruct (trichotomy 0 n) as [Heq | [Hpos | Hneg]]; apply (Hind n); intros k Hk.
    + subst n. destruct Hk. apply ord_antisym in H. contradiction.
    + destruct (excluded_middle_informative (P k)) as [Hpk | Hnpk]; auto.
      exfalso. apply Hno. exists k. split; try assumption. tauto.
    + destruct Hk. pose proof (ord_trans 0 k n H H0). apply ord_antisym in H1. contradiction.
Qed.
Theorem weak_induction : ∀ P : Z → Prop,
      P 1 → (∀ k, P k → P (k + 1)) → ∀ n : Z, 0 < n → P n.
    Proof.
    intros P H H0 n H1.
    induction n as [n H3] using A3P6.
    destruct (A3P1 1 n) as [H2 | [H2 | H2]].
    - have ->: n = (n - 1) + 1 by rewrite -add_assoc A1P2 A1P1.
      apply H0.
      rewrite A3P2 in H2.
      apply H3.
      + split.
        * trivial.
        * rewrite A3P2 /sub -A1P8 mul_comm mul_distr_r A1P9 A1P3 mul_comm
                               A1P8 add_assoc add_inv_r add_0_l.
          exact A3P3.
      + trivial.
    - rewrite -H2.
      exact H.
    - contradiction (A3P4 n).
      easy.
Qed.

(*parts of A4 collaborated with Jerry Du, Erix Xu, Jackie Zou, and Susan Ho*)
Theorem A4P1 : ∀ a b : Z, 0 < a → (0 < b ↔ 0 < a * b).
  intros; split. intros.
  pose proof (ord_mul 0 a b H0 H). rewrite A1P7 in H1; easy. exact (ord_mul_rev a b H).
Qed.

Lemma ord_lt_leq : ∀ a i : Z, i < a → i + 1 ≤ a.
  intros.
  destruct (trichotomy (i+1) a) as [H0 | [H1|H2]].
  firstorder. firstorder. exfalso. pose proof (dne_nonint a i). firstorder.
Qed.
Lemma ord_nlt_geq : ∀ a b : Z, ¬ a < b → a ≥ b.
  intros ???.
  destruct (trichotomy a b) as [H1|[H1|H1]].
  unfold "≤". right. symmetry. exact. exfalso. contradiction. unfold "≤". left. exact.
Qed.

(* Well-ordering principle *)
Theorem A4P2 : ∀ S : Z → Prop, (∀ x : Z, S x → 0 < x) → (∃ x : Z, S x) →
                                 ∃ s : Z, S s ∧ ∀ t : Z, S t → s ≤ t.
  intros S H [z H0]. 
  apply H in H0 as H1.
  pose proof H1 as H2.
  revert S H0 H2 H.
  elim/weak_induction: H1.
  - intros S H0 H H1. exists 1.
    split; auto. intros t H2. apply H1 in H2.
    apply ord_lt_leq in H2. rewrite add_0_l in H2. exact.
  - intros k H P H0 H1. clear z.
    destruct (classic (P k)); auto.
    destruct (classic (0 < k)).
    * intros H4.
      set (P' := (λ x, P x ∨ x = k)).
      destruct (H P') as [x [H5 H6]].
      unfold P'. right. reflexivity. auto. unfold P'.
      intros x [H5 | H5]; auto. congruence.
      destruct (A3P1 x k) as [H7 | [H7 | H7]].
        ++ exists x.
          split.
          ** destruct H5 as [H5 | H5].
               --- auto.
               --- subst. contradiction (ord_irrefl k).
          ** intros. apply H6.
               unfold P'.
               left. auto.
        ++ subst. exists (k + 1).
          split; auto.
          intros t H7.
          assert (k ≤ t).
          { apply H6. left. auto. }
          assert (k ≠ t).
          { intros H9. subst. contradiction. }
          destruct H8. apply ord_lt_leq in H8. exact. exfalso. exact.
         ++ exists (k + 1).
            split; auto.
            intros t H8.
            assert (x ≤ t). { apply H6. left. auto. }
            destruct H9. 
            pose proof (ord_trans k x t H7 H9).  apply ord_lt_leq in H10. exact.
            apply ord_lt_leq in H7. rewrite H9 in H7. exact.
    * assert (k = 0).
        {apply ord_nlt_geq in H3. destruct H3. apply (ord_add k 0 1) in H3. 
          rewrite add_0_l in H3. contradiction (A3P4 (k+1)). auto. auto. }
        intros H5. exists 1; subst.
        rewrite add_0_l in H0.
        split; auto. 
        intros t H6.
        apply H5 in H6.
        apply ord_lt_leq in H6. rewrite add_0_l in H6. exact.
Qed.

(* Euclidean division *)
Theorem A4P3 : ∀ a b : Z, b ≠ 0 → ∃ q r : Z, a = b * q + r ∧ 0 ≤ r < abs b.
  Proof.
  intros ???.
  wlog Hpos : b H / 0 < b.
  { intros.
    pose proof (trichotomy b 0). destruct H1.
    - exfalso; eauto.
    - destruct H1. 
      destruct (H0 (-b)).
      intros ?. apply (f_equal (add^~ b)) in H2. 
      rewrite add_0_l add_comm add_inv_r in H2; eauto.
      + apply (ord_neg b) in H1. rewrite minus_0_eq_0 in H1. trivial.
      + rewrite -(abs_neg b) in H2.
        exists (-x).
        rewrite (mul_neg_comm b x) in H2; apply H2.
      + firstorder. }
  assert (abs b = b) as Habs.
    {unfold abs. destruct excluded_middle_informative. reflexivity. exfalso. contradiction. }
  wlog Hapos : a / 0 < a.
  { intros.
    pose proof (trichotomy a 0). destruct H1.
    - rewrite H1. exists 0, 0. split. 
      rewrite mul_comm A1P7 add_0_l. trivial.
      pose proof (abs_nonneg b). 
      rewrite Habs. split. unfold "≤". right. reflexivity. exact Hpos.
    - destruct H1. destruct (H0 (-a)).
      apply (ord_add a 0 (-a)) in H1. 
      rewrite add_0_l add_inv_r in H1; trivial.
      destruct H2 as [r [H2 H3]].
      repeat destruct H3. 
      apply neg_refl in H2.
      rewrite (add_neg_dist (b*x) r) (mul_neg_dist) in H2.
      apply (f_equal (add^~ (-b+b))) in H2.
      rewrite {1}(add_comm (-b) b) {1}add_inv_r add_comm add_0_l 
      add_assoc (add_comm (b*-x)(-r)) -(add_assoc (-r)(b*-x)) -(A1P8 b) 
      mul_comm -mul_distr_r (add_comm (-r)) -add_assoc mul_comm in H2.
      + exists (-x-1), (-r+b).
        split. unfold sub. exact H2.
        split.
        rewrite Habs in H4.
        apply ord_neg, (ord_add (-b) (-r) b) in H4.
        rewrite add_comm add_inv_r in H4.
        apply A3P0 in H4. exact H4.
        rewrite Habs.
        apply ord_neg, (ord_add (-r) (-0) b) in H3.
        rewrite minus_0_eq_0 add_0_l in H3. 
        exact H3.
      + rewrite add_comm add_0_l in H2.
        apply neg_refl in H2.
        rewrite mul_neg_dist in H2.
        exists (-x), 0.
        rewrite add_comm add_0_l; firstorder.
      + apply H0; exact H1. }
  set (S := fun r : Z => (b | a - r) ∧ 0 ≤ r).
  assert (S ≠ Empty_set Z).
  {apply existence. unfold S. exists a.
    split. exists 0. unfold sub. rewrite add_inv_r A1P7. reflexivity.
    apply A3P0 in Hapos. exact Hapos. }
  assert (bounded_below S).
  {unfold bounded_below. exists (-1).
        intros t [Htpos]. destruct H1. pose proof (ord_trans (-1) 0 t n1_lt_0 H1). exact H2. 
        rewrite -H1. exact n1_lt_0. }
  pose proof (WOP S H0 H1) as [r H2].
  destruct H2. destruct H2. destruct H2.
  apply (f_equal (add^~ r)) in H2.
  rewrite -add_assoc (add_comm (-r)) add_inv_r add_comm add_0_l mul_comm in H2.
  exists x, r.
  split. exact. split. exact. rewrite Habs.
  destruct (classic (r<b)); auto.
  exfalso. apply ord_nlt_geq in H5. destruct H5.
  - assert (S (r-b)).
    {unfold S; split. 
      rewrite H2.
      unfold sub.
      exists (x+1).
      rewrite (add_neg_dist r (-b)) A1P6 add_assoc -(add_assoc (b*x) r) add_inv_r -add_assoc add_0_l.
      rewrite mul_distr_r mul_1_l mul_comm. reflexivity.
      apply (ord_add b r (-b)) in H5.
      rewrite add_inv_r in H5. unfold sub, "≤". auto. }
    destruct (H3 (r-b) H6).
    apply A3P2. unfold sub. rewrite (add_neg_dist r) A1P6 add_assoc add_inv_r add_0_l. exact.
  - assert (S (r-b)).
    {unfold S. split.
      rewrite H2.
      unfold sub.
      exists (x+1).
      rewrite (add_neg_dist r (-b)) A1P6 add_assoc -(add_assoc (b*x) r) add_inv_r -add_assoc add_0_l.
      rewrite mul_distr_r mul_1_l mul_comm. reflexivity.
      rewrite H5. unfold sub , "≤". rewrite add_inv_r. right. reflexivity. }
    destruct (H3 (r-b) H6).
    apply A3P2. unfold sub. rewrite (add_neg_dist r) A1P6 add_assoc add_inv_r add_0_l. exact.
Qed.

(* Helper lemmas *)
Lemma rel_prime_sym : ∀ a b : Z, rel_prime a b ↔ rel_prime b a.
    firstorder.
Qed.

Lemma rel_prime_1 : ∀ a : Z, rel_prime a 1.
    firstorder.
Qed.

Theorem A4P4 : ∀ a : Z, rel_prime a 0 ↔ unit a.
  Proof.
  split. intros.
  unfold rel_prime in H.
  destruct (H a).
  exact (divide_refl a). exact (divide_zero_all a). unfold unit, divide. exists x. exact.
  intros. unfold rel_prime.
  apply A2P4 in H. 
  destruct H; intros; unfold unit; rewrite H in H0; try exact.
  apply (divide_neg d (- 1)) in H0. rewrite A1P6 in H0. exact.
Qed.

Theorem A4P5 : ∀ a b : Z, rel_prime a b ↔ rel_prime a (-b).
  Proof.
  split. intros ????.
  unfold rel_prime in H.
  -destruct (H d H0).
  +apply (divide_neg) in H1. rewrite A1P6 in H1. exact.
  +unfold unit, divide. exists x. exact H2.
  -intros ????.
  unfold rel_prime in H.
  destruct (H d H0).
  +apply (divide_neg) in H1. exact.
  +unfold unit, divide. exists x. exact H2.
Qed.

Theorem A4P6 : ∀ a b c : Z, (a | b) → rel_prime b c → rel_prime a c.
  Proof.
  intros ????????.
  destruct (H0 d). apply (A2P2 d a b H1 H). exact.
  unfold unit, divide. exists x. exact.
Qed.
(*certain parts of A5 collaborated with Jerry Du, Erix Xu, Jackie Zou, and Susan Ho*)
Lemma assoc_self : ∀ a : Z, a~a.
  intros. split. exact (divide_refl a). exact (divide_refl a).
Qed.
Lemma assoc_comm : ∀ a b : Z, a ~ b → b ~ a.
  intros. unfold assoc. unfold assoc in H. destruct H. auto.
Qed.
Lemma assoc_neg : ∀ a : Z, a ~ -a.
  intros. split. 
  pose proof (divide_neg a a (divide_refl a)). exact.
  pose proof (divide_neg (-a) (-a) (divide_refl (-a))). rewrite A1P6 in H. exact.
Qed.
Theorem abs_to_assoc : ∀ a b : Z, abs a = b → a = ± b.
  intros. unfold abs in H. unfold pm.
  destruct excluded_middle_informative in H; auto. 
  apply neg_refl in H; auto.
Qed.

Theorem A5P4 : ∀ a b : Z, a ~ b ↔ a = ± b.
  split; intros.
  - destruct H; destruct H, H0.
    rewrite H mul_assoc mul_comm in H0. symmetry in H0. 
    destruct (classic (a=0)).
    + rewrite H1 mul_comm A1P7 in H. rewrite H H1. unfold pm. eauto. 
    + assert (x0*x = 1). apply (A1P11 a (x0*x)); eauto.
      assert (unit x). exists x0; auto.
      apply A2P4 in H3. destruct H3.
      * rewrite H3 mul_1_l in H. unfold pm. left. exact.
      * rewrite H3 A1P8 in H. unfold pm. right. rewrite H A1P6. exact.
  - destruct H. rewrite H. exact (assoc_self b). 
  rewrite H. pose proof (assoc_neg (-b)). rewrite A1P6 in H0. exact.
Qed.
Theorem pm_refl : ∀ a b : Z, pm a b → pm b a.
  intros. unfold pm. unfold pm in H. destruct H; auto. subst. right. ring.
Qed.
Theorem prove_by_order : ∀ a b : Z, a ≥ b ∧ b ≥ a → a = b.
  intros.
  destruct H. destruct (trichotomy a b) as [H1|[H1|H1]].
  - exact.
  - exfalso. destruct H. apply (ord_antisym) in H. exact. apply (ord_neq) in H. exact.
    exfalso. destruct H. apply (ord_neq) in H1. exact.
  - exfalso. destruct H0. apply (ord_antisym) in H0. exact. apply (ord_neq) in H0. exact.
    exfalso. symmetry in H0. apply (ord_neq) in H1. exact.
Qed.
Definition gcd (a b d : Z) : Prop :=
(d | a) ∧ (d | b) ∧ (∀ c : Z, (c | a) → (c | b) → (c | d)).
Lemma rel_prime_gcd1 : ∀ a b : Z, gcd a b 1 ↔ rel_prime a b.
  split. intros ????.
  - unfold gcd in H. destruct H. destruct H2. apply (H3 d H0 H1).
  - intros. unfold rel_prime in H. unfold gcd. 
    pose proof (one_divides_all a). pose proof (one_divides_all b). exact.
Qed.

(* Euclidean algorithm / Bezout's lemma *)
Theorem A5P1 : ∀ a b : Z, rel_prime a b → ∃ x y, a * x + b * y = 1.
  intros.
  wlog Hwlog : /(∃ x y : Z, a * x + b * y = ± 1) → (∃ x y : Z, a * x + b * y = 1).
  {intros Hwlog. apply Hwlog. intros Hpm. destruct Hpm as [x [y [Hp|Hm]]].
    exists x, y. exact. exists (-1*x), (-1*y). rewrite mul_assoc mul_assoc (mul_comm a) (mul_comm b).
    rewrite -mul_assoc -mul_assoc mul_comm (mul_comm (-1)) -mul_distr_r Hm A1P8 A1P6. exact. }
  set (S := fun k =>  k > 0 ∧ (∃ x y, a * x + b * y = k) ).
  assert (S≠Empty_set Z). 
  {apply existence. unfold S. 
    destruct (trichotomy 0 a) as [H0|[H0|H0]]. symmetry in H0.
    - destruct (trichotomy 0 b) as [H1|[H1|H1]]. 
      + exfalso. symmetry in H1. rewrite H0 H1 in H. apply A4P4, A2P4 in H. destruct H. 
        * pose proof (A2P3). exact.
        * pose proof (n1_lt_0). apply ord_neq in H2. symmetry in H. exact.
      + exists b. split. exact.
        exists 0, 1. rewrite mul_comm A1P7 add_0_l mul_comm mul_1_l. exact. 
      + exists (-b).
        apply (ord_neg b 0) in H1 as H2. rewrite minus_0_eq_0 in H2. split. exact.
        exists 0, (-1). rewrite mul_comm A1P7 add_0_l mul_comm A1P8. exact.
    - exists a. split. exact.
      exists 1, 0. rewrite (mul_comm b) A1P7 add_comm add_0_l mul_comm mul_1_l. exact.
    - exists (-a). split. apply ord_neg in H0. rewrite minus_0_eq_0 in H0. exact.
      exists (-1), 0. rewrite (mul_comm b) A1P7 add_comm add_0_l mul_comm A1P8. exact. }
  assert (bounded_below S).
  { unfold bounded_below; exists 0; intros t [Htpos _]; exact Htpos. }
  pose proof (WOP S H0 H1) as [d [Hd Hbound]].
  destruct Hd as [Hd0 [x [y Hd]]].
  assert (d≠0) as Hdn0. {apply ord_neq in Hd0. auto. }
  assert (d=abs d) as Hdabs. {unfold abs. destruct(excluded_middle_informative). exact. exfalso. exact. }
  assert (da : (d | a)).
  { pose proof (A4P3 a d Hdn0).
    destruct H2 as [q [r H2]].
    destruct (trichotomy r 0) as [Hr_eq | [Hr_pos | Hr_neg]].
    - subst r. exists q. rewrite mul_comm add_comm add_0_l in H2. destruct H2. exact.
    - exfalso. 
      destruct H2, H3, H3. apply ord_antisym in H3. exact.
      apply ord_neq in Hr_pos. symmetry in H3. exact.
    - exfalso. apply (Hbound r). unfold "∈", S. split; auto.
      + destruct H2, H3. 
        apply (f_equal (add^~ (-(d*q)))) in H2.
        rewrite (add_comm (d*q)) -add_assoc add_inv_r (add_comm r) add_0_l (mul_neg_dist) -Hd mul_distr_r 
          add_assoc -mul_assoc mul_comm -{1}(mul_1_l a) -mul_distr_r -mul_assoc mul_comm in H2.
        exists (1 + x * - q), (y * - q). exact.
      + destruct H2, H3. rewrite Hdabs. exact. }
      
  assert (db : (d | b)).
  { pose proof (A4P3 b d Hdn0).
    destruct H2 as [q [r H2]].
    destruct (trichotomy r 0) as [Hr_eq | [Hr_pos | Hr_neg]].
    - subst r. exists q. rewrite mul_comm add_comm add_0_l in H2. destruct H2. exact.
    - exfalso. 
      destruct H2, H2, H3. destruct H2. apply ord_antisym in H2. exact.
      apply ord_neq in Hr_pos. symmetry in H2. exact.
    - exfalso. apply (Hbound r). unfold "∈", S. split.
      + exact.
      + destruct H2, H3. 
        apply (f_equal (add^~ (-(d*q)))) in H2.
        rewrite (add_comm (d*q)) -add_assoc add_inv_r (add_comm r) add_0_l in H2.
        rewrite (mul_neg_dist) -Hd mul_distr_r add_assoc add_comm add_assoc in H2.
        rewrite -mul_assoc mul_comm -{2}(mul_1_l b) -mul_distr_r add_comm in H2.
        rewrite (mul_comm (y * - q + 1)) -mul_assoc in H2.
        exists (x * - q), (y * - q + 1). exact.
      + destruct H2, H3. rewrite Hdabs. exact. }
  apply (rel_prime_gcd1 a b) in H as Hgcd.
  unfold gcd in Hgcd. destruct Hgcd as [Ha [Hb Hc]].
  destruct (Hc d da db); auto.
  assert (unit d) as d1. unfold unit; eauto.
  apply Hwlog. unfold pm.
  apply A2P4 in d1. destruct d1; exists x, y; rewrite -H3; auto.
Qed.

(* Gauss's lemma *)
Theorem A5P2 : ∀ a b c : Z, rel_prime a b → (a | b * c) → (a | c).
  intros a b c Hrel Hdiv. 
  apply A5P1 in Hrel as H.
  destruct H as [x[y H]]. 
  destruct Hdiv as [z Hdiv].
  apply (f_equal (mul^~ c)) in H.
  rewrite mul_distr_r mul_1_l (mul_comm b) -(mul_assoc y) in H.
  rewrite Hdiv mul_assoc -mul_assoc mul_comm -mul_distr_r in H.
  symmetry in H.
  exists (x * c + y * z);exact.
Qed.

Lemma mul_distr_l : ∀ c a b : Z, c * (a + b)  = c * a + c * b.
  intros. ring.
Qed.
Theorem A5P3 : ∀ a b c : Z, rel_prime a b → (a | c) → (b | c) → (a * b | c).
  intros a b c Hrel Ha Hb.
  apply A5P1 in Hrel as H.
  destruct Ha as [y Ha]. destruct Hb as [z Hb].
  rewrite mul_comm in Ha, Hb.
  destruct H as [m[n H]]. 
  apply (f_equal (mul^~ c)) in H.
  rewrite mul_distr_r mul_1_l (mul_comm b) mul_comm mul_assoc (mul_comm c) (mul_comm n) in H.
  rewrite -(mul_assoc b) (mul_comm n) mul_assoc {1}Hb {1}Ha  (mul_comm z) mul_assoc in H. 
  rewrite mul_assoc (mul_comm b) -mul_assoc -(mul_assoc (a*b) y n) -(mul_distr_l (a*b)) mul_comm in H.
  exists (z * m + y * n); auto.
Qed.

(*ensured that prime and irreducible are equivalent in integral domains,
including this Z.*)
Lemma two_gt_0: 0 < 1 + 1.
  pose proof (z_lt_1).
  apply (ord_add 0 1 1) in H as H1. rewrite add_0_l in H1.
  apply (ord_trans 0 1 (1+1) H) in H1 .
  exact.
Qed.

Lemma zero_irred: ∀ p : Z, irreducible p → p ≠ 0.
  intros. intro. 
  destruct H as [H H1].
  destruct (H1 (1+1)).
  exists 0. rewrite A1P7. exact.
  apply A2P4 in H2. destruct H2. 
  apply (f_equal (add^~ -1)) in H2.
  rewrite -add_assoc add_inv_r add_comm add_0_l in H2. 
  symmetry in H2. contradiction A2P3.
  assert (1 + 1 > -1).
    {pose proof (ord_trans (-1) 0 1 n1_lt_0 z_lt_1).
      pose proof (z_lt_1). apply (ord_add 0 1 1) in H4. rewrite add_0_l in H4.
      exact (ord_trans (-1) 1 (1+1) H3 H4). }
  symmetry in H2. apply ord_neq in H3. exact.
  unfold assoc in H2. destruct H2. destruct H3. 
  rewrite H0 mul_comm A1P7 in H3.
  pose proof two_gt_0. symmetry in H3. apply ord_neq in H4. exact.
Qed.
Theorem prime_eq_irred : ∀ p : Z, prime p ↔ irreducible p.
  split; intros.
  - unfold prime in H. destruct H, H0.
    unfold irreducible; split; auto.
    + intros. destruct H2 as [z H2].
      destruct (H1 z d).
      * exists 1. rewrite mul_1_l. symmetry. exact.
      * left. unfold unit.
        destruct H3. 
        rewrite mul_comm H3 mul_assoc mul_comm (mul_comm d)in H2.
        symmetry in H2.
        pose proof (A1P11). destruct (H4 p (x*d)). split. 
        exact. exact. exists x. exact.
      * right. unfold assoc. split. 
        exists z; auto. auto.
  - apply (zero_irred p) in H as Hpne0.
    unfold irreducible in H. destruct H as [Hnu Hdivp].
    unfold prime. split; [ exact Hpne0 | split; [ exact Hnu | ] ].
    intros a b Hdiv.
    destruct (classic (p | a)) as [Hp_a | Hnp_a]; auto.
    + right.
      assert (Hrel: rel_prime p a).
      { intros d Hd_p Hd_a.
        destruct (Hdivp d Hd_p) as [Hunit | Hassoc]; auto.
          destruct Hassoc as [_ Hpd].
          pose proof (A2P2 p d a Hpd Hd_a) as H. contradiction. }
      apply (A5P2 p a b Hrel Hdiv).
Qed.

Lemma neq_refl : ∀ a b : Z, a ≠ b → b ≠ a.
  intros ????. symmetry in H0. contradiction.
Qed.
Lemma divide_n0 : ∀ a b : Z, (a | b) → b ≠ 0 → a ≠ 0.
  intros ?????. destruct H. rewrite H1 mul_comm A1P7 in H. contradiction.
Qed.
Lemma abs_red : ∀ a : Z, abs (abs a) = abs a.
  intro. 
  pose proof (abs_nonneg a).
  set b := abs a.
  destruct H.
  unfold abs; destruct (excluded_middle_informative).
  exact. exfalso. exact.
  unfold abs; destruct (excluded_middle_informative).
  exact. subst b. rewrite -H minus_0_eq_0. exact.
Qed.
Lemma abs1_eq_1 : abs 1 = 1.
  pose proof (z_lt_1). unfold abs. destruct (excluded_middle_informative).
  exact. exfalso. exact.
Qed.
Theorem A5P5 : irreducible (1 + 1).
  unfold irreducible. 
  pose proof (two_gt_0). split. 
  - intro. apply A2P4 in H0. destruct H0.
    symmetry in H0.
    pose proof (z_lt_1). apply (ord_neq) in H1.
    apply (f_equal (add^~ (-1))) in H0.
    rewrite -add_assoc add_inv_r add_comm add_0_l in H0. exact. 
    pose proof (n1_lt_0). rewrite -H0 in H1.
    apply ord_antisym in H1. exact.
  - intros. 
  pose proof two_gt_0 as Hn0. apply ord_neq, neq_refl in Hn0. 
  pose proof (A3P5 d (1+1) H0 Hn0) as H1.
  pose proof (one_divides_all (abs d)).
  pose proof (divide_n0 d (1+1) H0 Hn0). 
    apply (absn0), ord_neq, neq_refl in H3.
  pose proof (A3P5 1 (abs d) H2 H3).
  rewrite abs_red abs1_eq_1 in H4.
  assert (abs(1+1) = 1 + 1).
  {unfold abs. destruct (excluded_middle_informative). exact. exfalso. exact. }
  rewrite H5 in H1.
  destruct H4.
  + destruct H1.
    * exfalso. pose proof (dne_nonint (abs d) 1). auto.
    * unfold abs in H1. destruct (excluded_middle_informative) in H1;
      right; apply A5P4; unfold pm; try auto. right. apply neg_refl. exact.
  + left. apply A5P4. symmetry in H4. apply abs_to_assoc in H4.
    apply pm_refl. exact.
Qed.
Theorem A5P6 : ∀ p a : Z, irreducible p → (p | a) ∨ rel_prime p a.
  Proof.
  intros. 
  destruct (classic (p | a)); auto.
  - destruct H. right. unfold rel_prime. intros.
    destruct (H1 d H2); auto. 
    exfalso. apply A5P4 in H4. destruct H4.
      + rewrite H4 in H3. rewrite -H4 in H0.
        pose proof (A2P2 d p a H2 H3); exact.
      + apply H0. 
        rewrite H4 in H3.
        destruct H3.
        exists (-x).
        rewrite -(mul_neg_comm x) in H3; exact.
Qed.
(*parts of A6 collaborated with Jerry Du, Erix Xu, Jackie Zou, and Susan Ho*)
Lemma NNPP_neg: ∀ P : Prop, P → ¬¬P.
  firstorder.
Qed.
Lemma Neg_conj: ∀ P Q : Prop, ¬(P ∧ Q) → ¬P ∨ ¬Q.
  intros. destruct (excluded_middle_informative P); try auto.
Qed.
Lemma Neg_disj: ∀ P Q : Prop, ¬(P ∨ Q) → ¬P ∧ ¬Q.
  auto.
Qed.
Lemma unit_abs1: ∀ a : Z, unit a ↔ abs a = 1.
  split. 
  - intros. apply A2P4 in H. unfold abs. 
  destruct H; destruct (excluded_middle_informative (0 < a));auto.
  exfalso. pose proof(z_lt_1). subst. exact.
  exfalso. pose proof(n1_lt_0). apply ord_antisym in o. subst. exact. subst; apply A1P6.
  - intros. unfold abs in H. destruct (excluded_middle_informative (0 < a)).
  exists 1. rewrite mul_1_l. exact. exists (-1). rewrite A1P8 H. exact. 
Qed.
Lemma Neg_forall: ∀ P : Z → Prop, ¬ (∀ a : Z, P a) → ∃ a : Z, ¬ P a.
  intros. apply NNPP. intro.
  apply H. intro. apply NNPP.
  intro. apply H0. exists a. exact.
Qed.
Lemma Imply_or: ∀ P Q : Prop, (P→Q) ↔ ¬P ∨ Q.
  split. intros. destruct (excluded_middle_informative P); try auto.
  intros. destruct H. exfalso. exact. exact.
Qed.
Theorem A6P1: ∀ p : Z, p ≠ 0 → ¬ unit p → ¬ irreducible p →
∃ d : Z, 1 < abs d < abs p ∧ (d | p).
Proof.
  intros. unfold irreducible in H1. 
  apply Neg_conj in H1; destruct H1. 
  exfalso; auto.
  apply Neg_forall in H1; destruct H1. rewrite (Imply_or (x | p)  (unit x ∨ x ~ p)) in H1.
  apply Neg_disj in H1; destruct H1. apply NNPP in H1. apply Neg_disj in H2. destruct H2.
  pose proof (divide_n0 x p H1 H).
  exists x. split. split. 
  rewrite (absn0) in H4. apply (ord_lt_leq) in H4. rewrite add_0_l in H4.
  destruct H4; try assumption. exfalso. symmetry in H4. rewrite -unit_abs1 in H4. exact.
  pose proof (A3P5 x p H1 H). destruct H5; try assumption.
  exfalso; apply H3, A5P4. unfold pm. unfold abs in H5.
  destruct (excluded_middle_informative (0<x)) in H5;
  destruct (excluded_middle_informative (0<p)) in H5; auto. rewrite -H5 A1P6; auto.
  left; rewrite -(A1P6 x) H5 A1P6. exact. exact.
Qed.

Theorem A6P2: ∀ p x : Z, prime p → 0 < p → 0 < x → (p | x) →
                        ∃ k, k * p = x ∧ 0 < k < x.
Proof.
  intros; destruct H2 as [k H2].
  exists k. split. symmetry in H2; exact.
  subst. rewrite mul_comm in H1. 
  pose proof (ord_mul_rev p k H0 H1).
  split; auto. rewrite mul_comm -{1}(mul_1_l k). 
  apply (ord_mul 1 p k H2).
  unfold prime in H; destruct H, H3. apply ord_lt_leq in H0. rewrite add_0_l in H0.
  destruct H0; auto.
  exfalso. assert (p | 1). {exists 1; rewrite -H0 mul_1_l; exact. }
  apply H3. unfold unit. exact. 
Qed.

(* Euclid's lemma *)
(*already proven the equivalence between prime and irreducibles*)
(* :P *)
Theorem A6P3 : ∀ p a b : Z, irreducible p → (p | a * b) → (p | a) ∨ (p | b).
Proof. 
  intros. apply prime_eq_irred. exact. exact.
Qed.
Lemma abs_pos : ∀ a:Z, 0 < a → a = abs a.
  intros. unfold abs. destruct (excluded_middle_informative (0<a)); auto. exfalso. exact.
Qed.
Lemma abs_npos : ∀ a : Z, ¬ 0 < a → -a = abs a.
  intros. unfold abs. destruct (excluded_middle_informative (0 < a)); exact.
Qed.
Lemma divide_abs: ∀ a b : Z, (a | b) ↔ (abs a | b).
  split. intros. unfold abs.
  destruct (excluded_middle_informative (0<a)); auto. destruct H. exists (-x).
  rewrite -A1P8 H A1P8 A1P9. exact.
  intros. unfold abs in H. destruct (excluded_middle_informative (0<a)); auto.
  destruct H. exists (-x). rewrite mul_neg_comm. exact.
Qed.
Lemma divide_denom_n0: ∀ a b : Z, (a | b) → b ≠ 0 → a ≠ 0.
  intros. intro. destruct H. subst. rewrite mul_comm A1P7 in H0. exact.
Qed.
(* Existence of prime (irreducible) divisors *)
Theorem A6P4 : ∀ n : Z, n ≠ 0 → ¬ unit n →
               (∃ p : Z, 0 < abs p ∧ irreducible p ∧ (p | n)).
Proof.
  set (S := fun k : Z => k > 0 → ¬ unit k → (∃ p : Z, 0 < abs p ∧ irreducible p ∧ (p | k))). intro.
  wlog: n / (n>0).
    {intros. destruct (trichotomy 0 n) as [Hn |[Hn | Hn]].
    - apply (H n). exfalso. auto. exact. exact.
    - apply (H n). auto. exact. exact.
    - apply ord_neg in Hn. rewrite minus_0_eq_0 in Hn.
      assert (-n≠0). intro. apply neg_refl in H2. rewrite minus_0_eq_0 in H2; exact.
      apply (H (-n)) in Hn as [p [Hpg0 [Hpi Hpd]]].
      exists p. split; auto. split; auto.
      apply divide_neg in Hpd. rewrite A1P6 in Hpd. exact. exact. 
      intro. apply H1. apply A2P4 in H3. unfold unit.
      destruct H3. exists (-1). rewrite A1P8 H3. exact.
      exists 1. apply (neg_refl n (-1)) in H3. rewrite A1P6 in H3. rewrite mul_1_l. exact.
  }
  intros.
  apply (A3P6 S) in H as Hind. apply (Hind H1). 
  intros m Hind. unfold S. intros. 
  apply ord_neq in H2 as H4. apply neq_refl in H4. apply abs_pos in H2 as Habs.
  destruct (excluded_middle_informative (irreducible m)).
  - exists m. rewrite (absn0) in H0.
    split; apply absn0 in H4; auto. split; auto. exact (divide_refl m).
  - apply Neg_conj in n0 as n1. 
    destruct n1. exfalso. exact.
    apply Neg_forall in H5. destruct H5.
    rewrite (Imply_or (x | m) (unit x ∨ x ~ m)) in H5.
    apply Neg_disj in H5. destruct H5.
    apply NNPP in H5. 
    apply Neg_disj in H6. destruct H6.
    pose proof (A3P5 x m H5 H4). rewrite -Habs in H8.
    pose proof (divide_denom_n0 x m H5 H4) as Hn0.
    destruct H8.
    + apply absn0 in Hn0.
      destruct (Hind (abs x)). split; auto. auto. 
      unfold unit. rewrite -divide_abs. exact.
      destruct H9 as [H10 [H11 H12]].
      exists x0. split; auto; split; auto.
      rewrite divide_abs in H5. 
      exact (A2P2 (x0) (abs x) m H12 H5).
    + exfalso. apply H7. split. apply divide_abs. rewrite H8. exact (divide_refl m).
      rewrite -H8. unfold abs. destruct (excluded_middle_informative (0 < x)).
      exact (divide_refl x). exists (-1). rewrite A1P8 A1P6. exact.
Qed.

Fixpoint product (L : list Z) :=
  match L with
  | nil => 1
  | p :: L => p * product L
  end.

Notation "∏ L" := (product L) (at level 50).

Infix "in" := List.In (at level 70).
Lemma prod_divide: ∀ x L, x in L → (x | ∏ L).
  intros. 
  induction L as [| a L IH]; simpl.
  - inversion H.
  - destruct H; subst. exists (∏ L). rewrite mul_comm. exact.
    specialize (IH H). destruct IH as [k Hk].
    exists (a * k). rewrite Hk. rewrite mul_assoc. exact.
Qed.
Theorem A6P5 : ∀ p L, prime p → (p | ∏ L) → ∃ x, x in L ∧ (p | x).
Proof.
  induction L; simpl.
  - intros. unfold prime in H. destruct H as [H [H1 H2]]. exact.
  - intros. 
    destruct (excluded_middle_informative (p | a)).
    + exists a. split; auto.
    + apply IHL in H as H1.
      destruct H1 as [x [H2 H3]]. exists x.
      pose proof (prod_divide x L H2).
      split; auto.
  exact (A2P6 p a (∏ L) H n H0).
Qed.

Lemma abs_mul_distr: ∀ a b : Z, abs (a*b) = (abs a) * (abs b).
  intros.
  destruct (excluded_middle_informative (0<a));destruct (excluded_middle_informative (0<b)).
  - pose proof (ord_mul 0 a b o0 o). rewrite A1P7 in H. 
    apply abs_pos in o, o0, H. rewrite -o -o0 -H. exact.
  - assert (¬ 0 < a * b). intro. apply n. apply ord_mul_rev in H. exact. exact.
    apply abs_pos in o. apply abs_npos in n, H. rewrite -o -n -H. apply mul_neg_dist.
  - assert (¬ 0 < a * b). intro. apply n. rewrite mul_comm in H. apply ord_mul_rev in H. exact. exact.
    apply abs_pos in o. apply abs_npos in n, H. rewrite -o -n -H. rewrite mul_comm (mul_comm (-a)). apply mul_neg_dist.
  - apply abs_npos in n as H, n0 as H0; rewrite -H -H0. rewrite A1P9. 
    destruct (trichotomy 0 a) as [Ha|[Ha|Ha]].
      subst a. rewrite A1P7 -abs0. reflexivity. exfalso; easy.
    + destruct (trichotomy 0 b) as [Hb|[Hb|Hb]].
      subst b. rewrite mul_comm A1P7 -abs0. reflexivity. exfalso; easy.
      * pose proof (ord_mul_nn00 a b Ha Hb) as Hp.
        apply abs_pos in Hp. rewrite -Hp. reflexivity.
Qed.

Lemma prime_abs : ∀ a : Z, prime a → prime (abs a).
  intros.
  destruct H as [H[H1 H2]]; split. 
  apply absn0 in H. apply absn0. rewrite abs_red. exact.
  split. intro. apply H1. apply divide_abs. exact.
  intros. apply divide_abs in H0. specialize (H2 a0 b H0); destruct H2.
  apply divide_abs in H2, H0; auto. apply divide_abs in H2, H0; auto.
Qed.
(* Existence of prime factorizations *)
Theorem A6P6 : ∀ n,
0 < n → ∃ L : list Z, n = ∏ L ∧ (∀ p, p in L → 0 < p ∧ prime p).
Proof.
  set (S := fun k : Z => k > 0 → ∃ L : list Z, k = ∏ L ∧ (∀ p, p in L → 0 < p ∧ prime p)).
  apply (A3P6 S); intros.
  destruct (excluded_middle_informative (unit n)).
  - apply A2P4 in u. 
    destruct u; exists nil; subst.
    + split; auto. intros. inversion H0.
    + apply ord_antisym in H1. contradiction n1_lt_0.
  - unfold S. intros. 
    destruct (excluded_middle_informative (irreducible n)).
    + exists (n :: nil); split.
      * simpl. rewrite A1P3; exact.
      * intros p Hp.
        simpl in Hp. destruct Hp.
        subst p. split; auto. apply prime_eq_irred; exact.
        inversion H1.
    + pose proof (ord_neq 0 n H0) as Hn0. apply neq_refl in Hn0.
      pose proof (A6P4 n Hn0 n0) as Hp.
      destruct Hp as [p [Hppos [Hi [q Hdiv]]]].
      assert (abs q < n).
      { assert (q|n) as temp. exists p. rewrite mul_comm; exact.
      pose proof (A3P5 q n temp Hn0) as t1; destruct t1.
      * apply abs_pos in H0. rewrite -H0 in H1. exact.
      * exfalso. destruct Hi as [Hn Hi]; apply Hn.
        rewrite Hdiv in H1. rewrite abs_mul_distr in H1.
        apply divide_abs in temp. pose proof (divide_denom_n0 (abs q) n temp Hn0).
        assert (abs p = 1). {apply (A1P11 (abs q) (abs p)). split. exact. exact. }
        unfold unit. rewrite divide_abs. rewrite H3. exact (one_divides_all 1). }
      assert (0 < abs q). 
      { apply absn0. intro. subst. rewrite A1P7 in Hn0. exact. }
      assert (S (abs q)). apply (H (abs q)); split; exact.
      apply H3 in H2; destruct H2 as [L [H2 H4]].
      exists (abs p :: L).
      split.
      * simpl. rewrite -H2.
        apply abs_pos in H0. rewrite {2}Hdiv abs_mul_distr mul_comm in H0. exact.
      * simpl. intros. destruct H5.
        --assert (0 < abs p).
          { apply absn0. intro. subst. rewrite mul_comm A1P7 in Hn0. exact. }
          rewrite H5 in H6; split. exact.
          rewrite -H5. apply prime_eq_irred, prime_abs in Hi. exact.
        --specialize (H4 p0 H5). exact.
Qed.

Definition positive_prime (p : Z) := 0 < p ∧ prime p.
Definition prime_factorization n L := n = ∏ L ∧ Forall positive_prime L.

Notation "n = ∏' L" := (prime_factorization n L) (at level 70).
Lemma prime_factorizations_are_factorizations : ∀ n L, n = ∏' L → n = ∏ L.
Proof.
    intros n L H.
    destruct H as [H H0].
    exact H.
Qed.

Lemma prod_app : ∀ L L' : list Z, (∏ L) * (∏ L') = ∏ (L ++ L').
Proof.
    by induction L; simpl; intros L'; rewrite -? IHL ? mul_1_l ? mul_assoc.
Qed.

Lemma prod_cons_app :
∀ (L L' : list Z) (p : Z), ∏ (L ++ p :: L') = p * (∏ (L ++ L')).
Proof.
    induction L; auto => L' p /=.
    by rewrite IHL ? mul_assoc (mul_comm a).
Qed.

Lemma perm_prod : ∀ L1 L2 : list Z, Permutation L1 L2 → ∏ L1 = ∏ L2.
Proof.
  intros L1 L2 H.
  by induction H; simpl; try congruence; rewrite ? mul_assoc (mul_comm x).
Qed.

Lemma perm_prime_fact : ∀ (n : Z) (L1 L2 : list Z),
Permutation L1 L2 → n = ∏' L1 → n = ∏' L2.
Proof.
  intros n L1 L2 H [H0 H1].
  rewrite /prime_factorization ? Forall_forall in H1 |-*.
  split; eauto using eq_trans, perm_prod, Permutation_in, Permutation_sym.
Qed.

Add Morphism product with signature (@Permutation Z) ==> eq as perm_prod_morph.
Proof.
  exact perm_prod.
Qed.

Add Morphism prime_factorization with signature
eq ==> (@Permutation Z) ==> iff as perm_prime_fact_morph.
Proof.
  split; eauto using perm_prime_fact, Permutation_sym.
Qed.

(* Re-statement of A6P6 *)
Theorem A7P0 : ∀ n, 0 < n → ∃ L : list Z, n = ∏' L.
Proof.
  intros n H.
  apply A6P6 in H as [L H].
  exists L.
  rewrite /prime_factorization Forall_forall; exact.
Qed.
Lemma prod_pos : ∀ L : list Z , Forall positive_prime L → 0 < ∏ L.
  intros.
  induction L. 
  - exact z_lt_1.
  - inversion H; subst x l.
  destruct H2 as [Hpos H2].
  apply IHL in H3.
  pose proof (ord_mul 0 a (∏ L) H3 Hpos); rewrite A1P7 in H0.
  simpl; exact.
Qed.
Theorem A7P1 : ∀ n L, n = ∏' L → 0 < n.
Proof.
  intros.
  unfold prime_factorization in H.
  destruct H as [H Hp].
  induction L; simpl.
  - simpl in H. rewrite H. exact z_lt_1.
  - inversion Hp; simpl; subst x l.
    destruct H2 as [Hpos H2].
    pose proof (prod_pos L H3).
    pose proof (ord_mul 0 a (∏ L) H0 Hpos); rewrite A1P7 in H1.
    simpl in H; subst; exact.
Qed.

Theorem A7P2 : ∀ L, 1 = ∏' L ↔ L = nil.
Proof.
  split; intros.
  - induction L; try simpl; auto.
    exfalso; inversion H.
    inversion H1; subst.
    destruct H4, H3, H4.  
    simpl in H0.
    assert (∏ L > 0). 
    {pose proof z_lt_1. rewrite H0 in H7.
      exact (ord_mul_rev a (∏ L) H2 H7). }
    apply ord_lt_leq in H2, H7. rewrite add_0_l in H2, H7.
    destruct H2; subst.
    + symmetry in H0. pose proof (ord_1_rev a (∏ L) H2 H0).
      destruct H7.
      * apply ord_antisym in H8. contradiction.
      * apply ord_neq, neq_refl in H8. contradiction.
    + apply H4. exists 1. ring_simplify. exact.
  - rewrite H.
    unfold "n = ∏' L"; split; constructor.
Qed.

Theorem A7P3 : ∀ p n L, 0 < p → n = ∏' L → prime p → (p | n) → p in L.
Proof.
  intros.
  unfold prime_factorization in H0.
  destruct H0 as [Hn Hpp].
  rewrite Hn in H2; clear Hn n.
  induction L; simpl in *.
  - destruct H1 as [_ [Hp _]].
    exfalso. apply Hp. unfold unit. exact H2.
  - inversion Hpp as [| a0 L0 [Ha0 Hap] HppL]; subst.
    destruct H1 as [_ [Hpnunit H1]].
    destruct (H1 a (∏ L) H2) as [Hdiv | HpL].
    + left; rewrite prime_eq_irred in Hap; destruct Hap.
      specialize (H3 p Hdiv); destruct H3.
      * exfalso. exact.
      * apply A5P4 in H3; destruct H3; try auto.
        exfalso. apply ord_neg in Ha0. 
        rewrite minus_0_eq_0 -H3 in Ha0.
        apply ord_antisym in H; exact.
    + right; apply IHL; try auto.
Qed.

Theorem A7P4 : ∀ n p L, n * p = ∏' (p :: L) → n = ∏' L.
Proof.
  intros.
  inversion H. 
  simpl in H0.
  inversion H1; subst x l.
  destruct H4, H3.
  rewrite (mul_comm p) in H0.
  pose proof (A2P5 n (∏ L) p H0 H3).
  split; try auto.
Qed.

(* Fundamental theorem of arithmetic, a.k.a. unique prime factorization. *)
Theorem A7P5 : ∀ n L1 L2, n = ∏' L1 → n = ∏' L2 → Permutation L1 L2.
Proof.
  intros n L1; revert n.
  induction L1 as [| p L1 IH]; simpl in *; intros; destruct H.
  - rewrite H in H0; simpl in H0.
    apply A7P2 in H0; rewrite H0.
    constructor.
  - simpl in H. inversion H1; subst x l.
    assert (p | n). by exists (∏ L1); rewrite mul_comm; exact.
    inversion H4 as [Hp0 Hp].
    pose proof (A7P3 p n L2 Hp0 H0 Hp H2).
    destruct H2 as [m H2]. rewrite H2 (mul_comm p _) in H.
    apply ord_neq, neq_refl in Hp0.
    pose proof (A2P5 m (∏ L1) p H Hp0).
    apply In_split in H3 as [l2_pre [l2_post Hsplit]].
    rewrite Hsplit in H0; destruct H0.
    rewrite prod_cons_app H2 (mul_comm p _) in H0.
    pose proof (A2P5 m (∏ (l2_pre ++ l2_post)) p H0 Hp0) as Hm2.
    assert (Hml2' : m = ∏' (l2_pre ++ l2_post)).
    {split. exact. apply Forall_app in H3; destruct H3.
      inversion H7; subst. apply Forall_app; auto. }
    assert (Hml1 : m = ∏' L1). by split; exact.
    specialize (IH m (l2_pre ++ l2_post) Hml1 Hml2').
    rewrite Hsplit. apply Permutation_cons_app; exact.
Qed.
End Z_Theory.
(* Arriving here for the seventh time feels like an accomplishment,
 and I am certain that it is an accomplishment indeed. *)
