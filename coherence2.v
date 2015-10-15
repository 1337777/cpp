(** SEMI ASSOCIATIVE COHERENCE  --  coherence2.v COQ 8.4pl3

This COQ text shows the semiassociativity completeness and coherence internal some encoding where associative coherence is the meta:
- MACLANE PENTAGON IS SOME RECURSIVE SQUARE !! This recursive square is the "functorial" parallel to the normalization/flattening of binary trees.
- the associative coherence comes before anything else, before the semiassociative completeness and before the semiassociative coherence.
- the associative coherence, by the recursive square lemma, critically reduce to the classification of the endomorphisms in the semiassociative category. This associative coherence do not lack some "Newman-style" lemma.
- the associative category is the meta of the semiassociative category, and 
      - the statement of semiassociative completeness shows this very clearly,
      - the semiassociative coherence is done in some internal ( "first/second order " ??) encoding relative to associative coherence, and it is possible to [Extraction] computation datatypes and programs, which would not be possible in some (yet to be found) too meta ( "higher-order" / COQ Gallina ) encoding
      - the semiassociative coherence do lack some "Newman-style" lemma where the codomain object is in normal form
- this file use Chlipala CPDT [crush]-ing style tactics, which simplify any goal hypothesis which can be destructed-inverted/injected/discriminated back into one single goal, and which intantiate any goal hypothesis or some given lemmas using everything available in the local context.
- this file do not yet distinguish [Prop] or [Set] for computation and, even if this can be sometimes avoided, this file do not hesitate to use the library [Program.Equality] [dependent destruction] which is some [destruct] followed by inversion/injection/discriminate cleaning which may use [eq_rect_eq] logical [Prop] axiom which allows to destruct/rewrite equalities between two dependent pairs.
- and the [dependent destruction] tactic is indeed the critical tactic which allows the common/usual way of reasoning in mathematics textbook. this is the item of COQ which is still very experimental/fragile and lack future refinement
- Noson Yanofsky talks about some Catalan categories to solve associative coherence in hes doctor text, may be the "functorial" normalization/flattening here is related to hes Catalan categories
- going further into more coherences, the applications of all such would not be something similar to the AAC tactics or CoqMT which already come with COQ... 
        - but first of all, the usual termination/consistency restriction of COQ is something which is difficult to justify.
        - going further into more coherences, the decidability/computability may be lost
        - therefore the correct software may not be [COQ] but something like [DEDUKTI MODULO], Frederic Blanqui may be the next person for seeking references
*)

(** * Imports

Make use of CPDT tactics. Make use of [dependent destruction] from [Program.Equality] library, which sometimes uses som axiom for the destruction of equality between two dependent pairs. *)

Require Import List Omega Equality.
Require Import CpdtTactics.
Require Import coherence.

Set Implicit Arguments.

(** * Memory

Some reminders from eailier coherence.v for proving semiassociative completeness. *)

Infix "/\0" := up_0 (at level 59, right associativity). (*/!\ .. LEVEL OF /\0 /\1 <o ~ ~~ SHALL BE LOWER THAN = ,
Infix "/\1" := up_1 (at level 61, right associativity) *)
Infix "~~" := same (at level 69, no associativity). (* just below = *)

Lemma th001 : forall A B (f : arrows A B), forall x y : A, lt_right (f x) (f y) -> lt_right x y.
Proof.
  exact lem033.
Defined. Hint Resolve th001.

Lemma th002 : forall A B (f: arrows A B), bracket_left_not_occurs_in f -> (bracket_left_occurs_in f -> Empty_set).
Proof.
  exact lem004600.
Defined. Hint Resolve th002.

Lemma th003 : forall A B (f: arrows A B), (bracket_left_occurs_in f -> Empty_set) -> bracket_left_not_occurs_in f.
Proof.
  exact lem004700.
Defined. Hint Resolve th003.

Lemma th004 : forall A B (f: arrows A B), bracket_left_occurs_in f + bracket_left_not_occurs_in f.
Proof.
  exact lem004510.
Defined. Hint Resolve th004.

Lemma th005 : forall A B (f : arrows A B), (bracket_left_occurs_in f -> Empty_set) -> forall x y : A, x <r y -> f x <r f y.
Proof.
   exact lem004800.
Defined. Hint Resolve th005.

Lemma th006 : forall A B (f : arrows A B), bracket_left_occurs_in f -> {x: A & {y : A & prod (x <r y) (f x <r f y -> Empty_set)}}.
Proof.
  exact lem004500.
Defined. Hint Resolve th006.

Lemma th007 : forall A B (f : arrows A B), (bracket_left_not_occurs_in f) -> (forall x y : A, lt_right x y -> lt_right (f x) (f y)).
Proof.
  intros; cut ((bracket_left_occurs_in f -> Empty_set)); auto. apply th002; auto.
Defined. Hint Resolve th007.

Lemma th008 : forall A B (f : arrows A B), bracket_left_occurs_in f -> {x: A & {y : A & prod (lt_right x y) (lt_right (f x) (f y) -> Empty_set)}}.
Proof.
  intros; destruct (th006 H) as (x & y & ? & ?); exists x, y; auto.
Defined. Hint Resolve th008.

Lemma th009 : forall A B (f : arrows A B), (forall x y : A, lt_right x y -> lt_right (f x) (f y)) -> (bracket_left_not_occurs_in f).
Proof.
  intros; cut (bracket_left_occurs_in f -> Empty_set); [auto | ].
  intros Hf; apply th008 in Hf; firstorder.
Defined. Hint Resolve th009.

(** * Endomorphisms in semiassociative category, [lengthinr] invariant 

Some other way to distinguish objects, other than [lt_right], is lacked. The type of this other way shall be something like [nat], which do not print the objects. *)

Lemma th010 : forall A B (f : arrows A B), bracket_left_not_occurs_in f
              -> { Heq : B = A & 
                               (match Heq in (_ = A0) return (arrows A A0) with
                                  | eq_refl => f
                                end) ~~ (unitt A) }.
Proof.
  induction 1; crush; esplit with (eq_refl _); crush;
  repeat match goal with
           | [ |- (_ /\1 _) ~~ unitt (?A /\0 ?A0) ] => apply same_trans with (g := (unitt A) /\1 (unitt A0)); auto
           | [ |- (_ <o _) ~~ unitt ?A ] => apply same_trans with (g := (unitt A) <o (unitt A)); auto
         end.
Defined. Hint Resolve th010.

Lemma th020 : forall A B (f : arrows A B), bracket_left_not_occurs_in f -> A = B.
Proof.
  intros; destruct (th010 H); symmetry; assumption.
Defined.

Fixpoint lengthin (A : objects) : nat :=
  match A with
    | letter _ => 1
    | A0 /\0 A1 => S (lengthin A0 + lengthin A1)
  end.

Fixpoint lengthinr (A : objects) : nat :=
  match A with
    | letter _ => O
    | A0 /\0 A1 => lengthin A1 + (lengthinr A0 + lengthinr A1)
  end.

Lemma th030 : forall  A B (f : arrows A B), lengthin B = lengthin A.
Proof.
  induction 1; crush.
Defined. Hint Immediate th030. (*Hint Rewrite th030 using assumption.*)

Lemma th040 : forall len A B (f : arrows A B), coherence.length f <= len -> lengthinr B <= lengthinr A.
Proof.
  induction len.
  * intros; cut (2 <= coherence.length f) ; crush.
  * destruct f; crush.
    assert ( coherence.length f1 <= len).
    { 
      cut ( coherence.length f1 * 2 <= S len );
      cut ( coherence.length f1 * 2 <= coherence.length f1 * coherence.length f2);
      cut (2 <= coherence.length f2);
      auto with zarith.
    }
    assert ( coherence.length f2 <= len).
    { 
      cut ( 2 * coherence.length f2 <= S len );
      cut ( 2 * coherence.length f2 <= coherence.length f1 * coherence.length f2);
      cut (2 <= coherence.length f1);
      auto with zarith.
    }
    specialize (th030 f2).
    crush' true fail.
    Show.
    assert ( coherence.length f1 <= len).
    { 
      cut ( coherence.length f1 + 2 <= S len );
      cut ( coherence.length f1 + 2 <= coherence.length f1 + coherence.length f2);
      cut (2 <= coherence.length f2);
      auto with zarith.
    }
    assert ( coherence.length f2 <= len).
    { 
      cut ( 2 + coherence.length f2 <= S len );
      cut ( 2 + coherence.length f2 <= coherence.length f1 + coherence.length f2);
      cut (2 <= coherence.length f1);
      auto with zarith.
    }
    crush' true fail.
Defined.

Lemma th050 : forall A B (f : arrows A B), lengthinr B <= lengthinr A.
Proof.
  intros; eapply th040 with (f := f); eauto.
Defined. Hint Immediate th050.

Lemma th060 : forall A B (f : arrows A B), bracket_left_not_occurs_in f -> lengthinr B = lengthinr A.
Proof.
  intros; symmetry; f_equal; eapply th020; eauto.
Defined. Hint Immediate th060. Hint Rewrite th060 using assumption.

Lemma th070 : forall len A B (f : arrows A B), coherence.length f <= len -> bracket_left_occurs_in f -> lengthinr B < lengthinr A.
Proof.
  induction len.
  * intros; cut (2 <= coherence.length f) ; crush.
  * destruct f; crush' true bracket_left_occurs_in.
    assert ( coherence.length f1 <= len).
    { 
      cut ( coherence.length f1 * 2 <= S len );
      cut ( coherence.length f1 * 2 <= coherence.length f1 * coherence.length f2);
      cut (2 <= coherence.length f2);
      auto with zarith.
    }
    assert ( coherence.length f2 <= len).
    { 
      cut ( 2 * coherence.length f2 <= S len );
      cut ( 2 * coherence.length f2 <= coherence.length f1 * coherence.length f2);
      cut (2 <= coherence.length f1);
      auto with zarith.
    }
    dependent destruction H0;
    specialize th030 with (1:=f2);
    assert (lengthinr B0 <= lengthinr A0) by auto;
    assert (lengthinr B <= lengthinr A) by auto;
    crush' true fail.
    Show.
    assert ( coherence.length f1 <= len).
    { 
      cut ( coherence.length f1 + 2 <= S len );
      cut ( coherence.length f1 + 2 <= coherence.length f1 + coherence.length f2);
      cut (2 <= coherence.length f2);
      auto with zarith.
    }
    assert ( coherence.length f2 <= len).
    { 
      cut ( 2 + coherence.length f2 <= S len );
      cut ( 2 + coherence.length f2 <= coherence.length f1 + coherence.length f2);
      cut (2 <= coherence.length f1);
      auto with zarith.
    }
    dependent destruction H0; 
      [ cut (lengthinr C < lengthinr B); [| apply IHlen with (f:=f2)] 
      | cut (lengthinr B < lengthinr A) ; [| apply IHlen with (f:=f1)] ];
      cut (lengthinr B <= lengthinr A);
      cut (lengthinr C <= lengthinr B); crush.
Defined.

Lemma th080 : forall A B (f : arrows A B), bracket_left_occurs_in f -> lengthinr B < lengthinr A.
Proof.
  intros; eapply th070 with (f := f); eauto.
Defined. Hint Resolve th080.

Lemma th090 : forall A B (f : arrows A B), bracket_left_occurs_in f -> lengthinr B = lengthinr A -> Empty_set.
Proof.
  intros; pose proof (th080); crush' true fail.
Defined. Hint Resolve th090.

Lemma th100 : forall A (f : arrows A A), bracket_left_not_occurs_in f.
Proof.
  intros; specialize th090; cut (lengthinr A = lengthinr A); cut (bracket_left_occurs_in f + bracket_left_not_occurs_in f); crush' true fail.
Defined. Hint Resolve th100.

(* ABORT
Lemma th110 : forall A (f : arrows A A), forall x, f x = x.
Proof.
  intros;
  cut (bracket_left_not_occurs_in f); [|auto].
  intros; revert x.
Abort.
*)

Lemma th110 : forall A B (f g : arrows A B), (f ~~ g) -> forall x : A, f x = g x.
Proof.
  induction 1; intros;
    repeat match goal with 
             | [xtac : nodes (_ /\0 _) |- _] => dep_destruct xtac; clear xtac
           end; crush.
Defined. Hint Resolve th110.

Lemma th120 : forall A (f : arrows A A), forall x, f x = x.
Proof.
  intros; assert (bracket_left_not_occurs_in f) by auto;
  destruct (th010 H) as [Heq Hsame];
  dependent destruction Heq;
  rewrite (th110 Hsame); reflexivity.
Defined. Hint Resolve th120.

(* ABORT
Lemma th130 : forall A B (f g : arrows A B), forall x, f x = g x.
Proof.
  intros.
  Fail assert ((com_assoc f (coherence.rev g)) x = x) by auto. 
Abort All.
*)

(* ABORT
Require Import Bool.
Fixpoint arrows_assoc_b (A B : objects) : bool.

refine (orb _ _).
* Check eqb. Check objects_beq. Check objects_eq_dec. exact (objects_beq A B).
* refine (_ || _).
  + exact (match A, B with
             | (A0 /\0 (B0 /\0 C0)) , ((A1 /\0 B1) /\0 C1) => (objects_beq A0 A1) && (objects_beq B0 B1) && (objects_beq C0 C1)
             | _ , _ => false
           end).
  + refine (_ || _).
    - exact (match A, B with
             | ((A0 /\0 B0) /\0 C0) , (A1 /\0 (B1 /\0 C1)) => (objects_beq A0 A1) && (objects_beq B0 B1) && (objects_beq C0 C1)
             | _ , _ => false
           end).
    - { refine (_ || _).
        * exact (match A, B with
                   | (A0 /\0 A1) , (B0 /\0 B1) => (arrows_assoc_b A0 B0) && (arrows_assoc_b A1 B1)
                   | _ , _ => false
                 end).
        * Check existsb. Guarded.
(*
| unitt_assoc : forall A : objects, arrows_assoc A A
| bracket_left_assoc : forall A B C : objects, arrows_assoc (A /\ (B /\ C)) ((A /\ B) /\ C)
| bracket_right_assoc : forall A B C : objects, arrows_assoc ((A /\ B) /\ C) (A /\ (B /\ C))
| up_1_assoc : forall A B A0 B0 : objects, arrows_assoc A B -> arrows_assoc A0 B0 -> arrows_assoc (A /\ A0) (B /\ B0)
| com_assoc : forall A B C : objects, arrows_assoc A B -> arrows_assoc B C -> arrows_assoc A C.
 *)
Abort All.
*)

(** * Functorial normalization for objects, which are simple binary trees *)

Inductive normal : objects -> Set :=
| normal_cons1 : forall l : letters, normal (letter l)
| normal_cons2 : forall (A : objects) (l : letters), normal A -> normal (A /\0 letter l).
Hint Constructors normal.

Reserved Notation "Z </\0 A" (at level 55, left associativity).

Fixpoint normalize_aux Z A {struct A} : objects :=
  match A with
    | letter l => Z /\0 letter l
    | A1 /\0 A2 => (Z </\0 A1) </\0 A2
  end
where "Z </\0 A" := (normalize_aux Z A).

Fixpoint normalize A : objects :=
  match A with
    | letter l => letter l
    | A1 /\0 A2 => (normalize A1) </\0 A2
  end.

Lemma th140 : forall A2 A1, normal A1 -> normal (A1 </\0 A2).
Proof.
  induction A2; simpl in *; intuition. 
Defined.
Hint Resolve th140.

Lemma th150 : forall A, normal (normalize A).
Proof.
  induction A; simpl in *; intuition.
Defined.
Hint Resolve th150.

Lemma th151 : forall A, normal A -> normalize A = A.
Proof.
  induction 1; simpl in *; [reflexivity|]; rewriter; reflexivity. (* [crush] /!\ bad *)
Defined.
Hint Resolve th151.

Lemma th152 : forall A, normalize (normalize A) = normalize A.
Proof.
  intros; apply th151; auto.
Defined.
Hint Resolve th152.

Inductive normal_aux (Z : objects) : objects -> Set :=
| normal_aux_cons1 : normal_aux Z Z
| normal_aux_cons2 : forall A l, normal_aux Z A -> normal_aux Z (A /\0 letter l).
Hint Constructors normal_aux.

Lemma th160 : forall B A Z, normal_aux Z A -> normal_aux Z (A </\0 B).
Proof.
  induction B; crush.
Defined.
Hint Resolve th160.

Lemma th170 : forall Z B, normal_aux Z (Z </\0 B).
Proof.
  auto.
Defined.
Hint Resolve th170.

Reserved Notation "y </\1 A" (at level 57, left associativity).

Fixpoint normalize_aux_arrow Y Z (y : arrows Y Z) A : arrows (Y /\0 A) (Z </\0 A) :=
  match A with
    | letter l => y /\1 unitt (letter l)
    | A1 /\0 A2 => ((y </\1 A1) </\1 A2) <o bracket_left Y A1 A2
  end
where "y </\1 A" := (normalize_aux_arrow y A).

Fixpoint normalize_arrow A : arrows A (normalize A) :=
  match A with
    | letter l => unitt (letter l)
    | A1 /\0 A2 => (normalize_arrow A1) </\1 A2
  end.


(* OLD NO PROGRESS
Fixpoint normalize_arrow (A:objects) : arrows A (normalize A).

destruct A.
simpl in *. exact (unitt (letter l)).
simpl in *.  induction A2 in A1 |- *.
   simpl in *. exact ((normalize_arrow A1) /\1 (unitt (letter l))).
   simpl in *. replace  (normalize_aux A2_1 (normalize A1)) with (normalize (A1 /\0 A2_1)) by auto.
   refine (_ <o bracket_left A1 A2_1 A2_2).
   apply IHA2_2.
Defined (*/!\ NO PROGRESS *). 
*)

(** * Simple normalization for developed arrows, which are more complicated than binary trees *)

Inductive developed_normal : forall A B, arrows A B -> Set :=
| developed_normal_unitt : forall A, developed_normal (unitt A)
| developed_normal_com : forall A B (g : arrows A B), term_bracket_left g -> forall C (f : arrows B C), developed_normal f -> developed_normal (f <o g).
Hint Constructors developed_normal.

Fixpoint developed_normal_coerce A B (f : arrows A B) (dev_normal_f : developed_normal f) {struct dev_normal_f} : developed f.
Proof.
  destruct dev_normal_f.
     constructor 1.

     constructor 3; crush.  
Defined.
Hint Resolve developed_normal_coerce.
Coercion developed_normal_coerce : developed_normal >-> developed.

Fixpoint developed_normalize_aux B C (fin : arrows B C) (dev_fin : developed fin) A (f : arrows A B) (dev_f : developed f) {struct dev_f} : {h : arrows A C & prod (developed h) ((fin <o f) ~~ h) }.
Proof.
  destruct dev_f.
     split with fin; crush.

     split with (fin <o f); crush.

     set (dev_fin_8f2 := (projT2 (developed_normalize_aux _ _ _ dev_fin _ _ dev_f2))) in |- ; simpl in dev_fin_8f2.
     set (fin_8f2 := (projT1 (developed_normalize_aux _ _ _ dev_fin _ _ dev_f2))) in *.
     set (dev_fin_8f2_8f1 := (projT2 (developed_normalize_aux _ _ _ (fst dev_fin_8f2) _ _ dev_f1))) in |- ; simpl in dev_fin_8f2_8f1.
     set (fin_8f2_8f1 := (projT1 (developed_normalize_aux _ _ _ (fst dev_fin_8f2) _ _ dev_f1))) in *.
     split with fin_8f2_8f1; crush; set (H_tmp := snd dev_fin_8f2) in |- ;
     apply same_trans with (g := ((fin <o g) <o f)); [auto|] ;
     apply same_trans with (g := fin_8f2 <o f); crush.
Defined.

Lemma th180 : forall A B (f : arrows A B) (dev_f : developed f) C (fin : arrows B C) (dev_fin : developed fin),
                developed_normal fin -> developed_normal (projT1 (developed_normalize_aux dev_fin dev_f)).
Proof.
  induction dev_f;
  crush.
Defined.
Hint Resolve th180.

Lemma th190 : forall A B (f : arrows A B) (dev_f : developed f) C (fin : arrows B C) (dev_normal_fin : developed_normal fin),
                developed_normal (projT1 (developed_normalize_aux dev_normal_fin dev_f)).
Proof.
  auto.
Defined.
Hint Resolve th190.
     
Fixpoint developed_normalize A B (f : arrows A B) (dev_f : developed f) {struct dev_f} : {h : arrows A B & prod (developed_normal h) (f ~~ h) }.
Proof.
  destruct dev_f.
     split with (unitt A); crush.

     split with ((unitt B) <o f); crush.

     set (dev_normal_f2' := projT2 (developed_normalize _ _ _ dev_f2)) in |- ; simpl in (type of dev_normal_f2').
     set (var_tmp := snd (projT2 (developed_normalize _ _ _ dev_f2))) in |- ; simpl in (type of var_tmp).
     set (f2' := projT1 (developed_normalize _ _ _ dev_f2)) in * .
     set (prop_f2'_f1' := snd (projT2 (developed_normalize_aux (fst dev_normal_f2') dev_f1))) in |- ; simpl in (type of prop_f2'_f1').
     set (f2'_f1' := (projT1 (developed_normalize_aux (fst dev_normal_f2') dev_f1))) in *.
     split with f2'_f1'; split; [subst f2'_f1'; trivial|].
     apply same_trans with (g := (f2' <o f)); [auto | assumption].
Defined.

(** ** OOPS, forgot same'_nat naturality of bracket_left in coherence.v *)

Inductive same' : forall A B : objects, arrows A B -> arrows A B -> Set := 
| same'_refl : forall A B f, @same' A B f f
| same'_trans : forall A B f g h, @same' A B f g -> @same' A B g h -> @same' A B f h
| same'_sym : forall A B f g, @same' A B f g -> @same' A B g f
| same'_cong_com : forall A B C f f0 g g0, @same' A B f f0 -> @same' B C g g0 ->
 @same' A C (g <o f) (g0 <o f0)
| same'_cong_up_1 : forall A B A0 B0 f f0 g g0, @same' A B f f0 -> @same' A0 B0 g g0 ->
 @same' (A /\0 A0) (B /\0 B0) (f /\1 g) (f0 /\1 g0)
| same'_cat_left : forall A B, forall f : arrows A B, @same' A B ( (unitt B) <o f ) ( f )
| same'_cat_right : forall A B, forall f : arrows A B, @same' A B ( f <o (unitt A)) ( f )
| same'_cat_assoc : forall A B C D, forall (f : arrows A B) (g : arrows B C) (h : arrows C D), @same' A D ( h <o (g <o f)  ) ( (h <o g) <o f  )
| same'_bif_up_unit : forall A B, @same' (A /\0 B) (A /\0 B) ((unitt A) /\1 (unitt B)) (unitt (A /\0 B))
| same'_bif_up_com : forall A B C A0 B0 C0, forall (f : arrows A B) (g : arrows B C) (f0 : arrows A0 B0) (g0 : arrows B0 C0), @same' (A /\0 A0) (C /\0 C0) ( (g <o f) /\1 (g0 <o f0) ) ( (g /\1 g0) <o (f /\1 f0) )
| same'_bracket_left_5 : forall A B C D, 
 @same' (A /\0 (B /\0 (C /\0 D))) ((((A /\0 B) /\0 C) /\0 D))
 ( (bracket_left (A /\0 B) C D) <o (bracket_left A B (C /\0 D)) )
 ( (bracket_left A B C) /\1 (unitt D)  <o (bracket_left A (B /\0 C) D) <o (unitt A) /\1 (bracket_left B C D) )
| same'_nat : forall A A' f B B' g C C' h, same' (bracket_left A B C <o (f /\1 (g /\1 h))) (((f /\1 g) /\1 h) <o bracket_left A' B' C').
Hint Constructors same'.
Infix "~~~" := same' (at level 69). (* just before = *)

Fixpoint same_to_same' A B (f g : arrows A B) (H_same_f_g : same f g) {struct H_same_f_g} : same' f g.
Proof.
  destruct H_same_f_g.
     constructor 1.
     constructor 2 with (g := g); apply same_to_same'; assumption.
     constructor 3; apply same_to_same'; assumption.
     constructor 4; apply same_to_same'; assumption.
     constructor 5; apply same_to_same'; assumption.
     constructor 6.
     constructor 7.
     constructor 8.
     constructor 9.
     constructor 10.
     constructor 11.
Defined.
Hint Resolve same_to_same'.
Coercion same_to_same' : same >-> same'.

(** ** Continue normalization for developed arrows *)

(* This was for training, not lacking anymore
Lemma th200_unrefined : forall N M1 (h1 : arrows N M1) (bra_h1 : term_bracket_left h1) M2 (h2 : arrows N M2) (bra_h2 : term_bracket_left h2),
                {P : objects & {h1' : arrows M1 P & {h2' : arrows M2 P & ((h1' <o h1) ~~~ (h2' <o h2)) }}}.
Proof.
  induction 1.
  - intros; dependent destruction bra_h2 (* NO PROGRESS inversion bra_h2. *).
    + esplit. exists (unitt _), (unitt _). apply same'_refl. (* [3] (struct conv) *)
    + esplit. exists ((f /\1 (unitt _)) /\1 (unitt _)), (bracket_left _ _ _);
              apply same'_trans with (g := (bracket_left _ B C <o f /\1 ((unitt _) /\1 (unitt _)))); crush (* [crush] bad when not [Prop] *). (* [2] (b nat) *)
    + dependent destruction bra_h2.
      * esplit. exists ( (bracket_left (A /\0 B) B0 C0) ), ( ((bracket_left A B B0) /\1 (unitt _)) <o (bracket_left A (B /\0 B0) C0) ). eapply same'_trans; [|eapply same'_cat_assoc]; apply same'_bracket_left_5. (* [4] (b 5) *)
      * esplit. exists (((unitt _) /\1 f0) /\1 (unitt _)), (bracket_left _ _ _). apply same'_sym, same'_nat. (* [2] (b nat) *)
      * esplit. exists (((unitt _) /\1 (unitt _)) /\1 f0), (bracket_left _ _ _). apply same'_sym, same'_nat. (* [2] (b nat) *)
  - intros; dependent destruction bra_h2.
    + esplit. exists (bracket_left _ _ _), ((f /\1 (unitt _)) /\1 (unitt _)). apply same'_trans with (g := bracket_left _ B0 C <o f /\1 (unitt _) /\1 (unitt _) ); crush. (* rev [2] (b nat) *)
    + esplit. set (prop_IH := (projT2 (projT2 (projT2 (IHbra_h1 _ _ bra_h2))))) in |- ; simpl in (type of prop_IH).
      set (h2'_IH := (projT1 (projT2 (projT2 (IHbra_h1 _ _ bra_h2))))) in * ; simpl in (type of h2'_IH).
      set (h1'_IH := (projT1 (projT2 (IHbra_h1 _ _ bra_h2)))) in * ; simpl in (type of h1'_IH).
      set (P_IH := (projT1 (IHbra_h1 _ _ bra_h2))) in * ; simpl in (type of P_IH).
      exists (h1'_IH /\1 (unitt _)), (h2'_IH /\1 (unitt _)).
      apply same'_trans with (g := (h1'_IH <o f) /\1 (unitt _ <o unitt _)); [auto|].
      apply same'_trans with (g := (h2'_IH <o f0) /\1 (unitt _ <o unitt _)); auto. (* (_ /\ unitt  induction) *)
    + esplit. exists (unitt _ /\1 f0), (f /\1 unitt _). 
      apply same'_trans with (g := (unitt _ <o f) /\1 (f0 <o unitt _)); [auto|].
      apply same'_trans with (g := (f <o unitt _) /\1 (unitt _ <o f0)); [|auto].
      apply same'_trans with (g := f /\1 f0); auto. (* [1] (/\ 2 bif) *)
  - intros; dependent destruction bra_h2.
    + dependent destruction bra_h1.
      * esplit. exists ( bracket_left A B B0 /\1 unitt _ <o bracket_left A (B /\0 B0) C0 ), ( bracket_left (A /\0 B) B0 C0 ). apply same'_sym; eapply same'_trans; [|eapply same'_cat_assoc]; apply same'_bracket_left_5. (* rev [4] (b 5) *)
      * esplit. exists (bracket_left _ _ _), ((unitt _ /\1 f0) /\1 unitt _). apply same'_nat. (* rev [2] (b nat) *)
      * esplit. exists  (bracket_left _ _ _), ((unitt _ /\1 unitt _) /\1 f0). apply same'_nat. (* rev [2] (b nat) *)
    + esplit. exists  (f0 /\1 unitt _), (unitt _ /\1 f). 
      apply same'_trans with (g := (f0 <o unitt _) /\1 (unitt _ <o f)); [auto|].
      apply same'_trans with (g := (unitt _ <o f0) /\1 (f <o unitt _)); [|auto].
      apply same'_trans with (g := f0 /\1 f); auto. (* rev [1] (/\ 2 bif) *)
    + esplit. set (prop_IH := (projT2 (projT2 (projT2 (IHbra_h1 _ _ bra_h2))))) in |- ; simpl in (type of prop_IH).
      set (h2'_IH := (projT1 (projT2 (projT2 (IHbra_h1 _ _ bra_h2))))) in * ; simpl in (type of h2'_IH).
      set (h1'_IH := (projT1 (projT2 (IHbra_h1 _ _ bra_h2)))) in * ; simpl in (type of h1'_IH).
      set (P_IH := (projT1 (IHbra_h1 _ _ bra_h2))) in * ; simpl in (type of P_IH).
      exists (unitt _ /\1 h1'_IH), (unitt _ /\1 h2'_IH).
      apply same'_trans with (g :=  (unitt _ <o unitt _) /\1 (h1'_IH <o f)); [auto|].
      apply same'_trans with (g := (unitt _ <o unitt _) /\1 (h2'_IH <o f0)); auto. (* (unitt /\ _  induction) *)
Defined.
*)

Hint Unfold unitt_on_nodes.

Lemma th200 : forall N M1 (h1 : arrows N M1) (bra_h1 : term_bracket_left h1) M2 (h2 : arrows N M2) (bra_h2 : term_bracket_left h2),
                {P : objects & {h1' : arrows M1 P & {h2' : arrows M2 P & 
                 prod ((h1' <o h1) ~~~ (h2' <o h2))
                 (forall x y : nodes P, (lt_right ((rev h1') x) ((rev h1') y)) -> (lt_right ((rev h2') x) ((rev h2') y)) -> lt_right x y) }}}.
Proof.
  induction 1.
  - intros; dependent destruction bra_h2 (* NO PROGRESS inversion bra_h2. *).
    + esplit. exists (unitt _), (unitt _).
      { split. 
        - apply same'_refl. (* [3] (struct conv) *)
        - crush.
      }
    + esplit. exists ((f /\1 (unitt _)) /\1 (unitt _)), (bracket_left _ _ _).
      { split.
        - apply same'_trans with (g := (bracket_left _ B C <o f /\1 ((unitt _) /\1 (unitt _)))); crush (* [crush] bad when not [Prop] *). (* [2] (b nat) *)
        - intros; repeat match goal with 
                           | [xtac : nodes (_ /\0 _) |- _] => dep_destruct xtac; clear xtac
                         end; crush' false lt_right.
      }
    + dependent destruction bra_h2.
      * esplit. exists ( (bracket_left (A /\0 B) B0 C0) ), ( ((bracket_left A B B0) /\1 (unitt _)) <o (bracket_left A (B /\0 B0) C0) ).
        { split.
          - eapply same'_trans; [|eapply same'_cat_assoc]; apply same'_bracket_left_5. (* [4] (b 5) *)
          - intros; repeat match goal with 
                           | [xtac : nodes (_ /\0 _) |- _] => dep_destruct xtac; clear xtac
                         end; crush' false lt_right. 
        }
      * esplit. exists (((unitt _) /\1 f0) /\1 (unitt _)), (bracket_left _ _ _). 
        { split. 
          - apply same'_sym, same'_nat. (* [2] (b nat) *)
          - intros; repeat match goal with 
                           | [xtac : nodes (_ /\0 _) |- _] => dep_destruct xtac; clear xtac
                         end; crush' false lt_right.
        }
      * esplit. exists (((unitt _) /\1 (unitt _)) /\1 f0), (bracket_left _ _ _). 
        { split.
          - apply same'_sym, same'_nat. (* [2] (b nat) *)
          - intros; repeat match goal with 
                             | [xtac : nodes (_ /\0 _) |- _] => dep_destruct xtac; clear xtac
                           end; crush' false lt_right.
        }
  - intros; dependent destruction bra_h2.
    + esplit. exists (bracket_left _ _ _), ((f /\1 (unitt _)) /\1 (unitt _)).
      { split.
        - apply same'_trans with (g := bracket_left _ B0 C <o f /\1 (unitt _) /\1 (unitt _) ); crush. (* rev [2] (b nat) *)
        - intros; repeat match goal with 
                           | [xtac : nodes (_ /\0 _) |- _] => dep_destruct xtac; clear xtac
                         end; crush' false lt_right.
      }
    + esplit. set (prop1_IH := fst (projT2 (projT2 (projT2 (IHbra_h1 _ _ bra_h2))))) in |- ; simpl in (type of prop1_IH).
      set (prop2_IH := snd (projT2 (projT2 (projT2 (IHbra_h1 _ _ bra_h2))))) in |- .
      set (h2'_IH := (projT1 (projT2 (projT2 (IHbra_h1 _ _ bra_h2))))) in (type of prop1_IH), (type of prop2_IH).
      set (h1'_IH := (projT1 (projT2 (IHbra_h1 _ _ bra_h2)))) in (type of h2'_IH), (type of prop1_IH), (type of prop2_IH).
      exists (h1'_IH /\1 (unitt _)), (h2'_IH /\1 (unitt _)).
      set (P_IH := (projT1 (IHbra_h1 _ _ bra_h2))) in (type of h1'_IH), (type of h2'_IH), (type of prop1_IH), (type of prop2_IH) |- *.
      { split.
        - apply same'_trans with (g := (h1'_IH <o f) /\1 (unitt _ <o unitt _)); [auto|].
          apply same'_trans with (g := (h2'_IH <o f0) /\1 (unitt _ <o unitt _)); auto. (* (_ /\ unitt  induction) *)
        - Fail generalize dependent P_IH.
          (* all these generalize because [crush] is bad with our fixed local definitions, for example [subst] ?? *)
          generalize prop2_IH; clear prop2_IH.
          generalize prop1_IH; clear prop1_IH.
          generalize h2'_IH; clear h2'_IH.
          generalize h1'_IH; clear h1'_IH.
          generalize P_IH; clear P_IH.
          clear bra_h2 IHbra_h1 bra_h1.
          intros; repeat match goal with 
                   | [xtac : nodes (_ /\0 _) |- _] => dep_destruct xtac; clear xtac
                 end; crush' false lt_right.
          (* OLD BAD MANUAL
          intros;
          repeat match goal with 
                   | [xtac : nodes (_ /\0 _) |- _] => dep_destruct xtac; clear xtac
                 end. (* crush' false lt_right. *)
          + crush' false lt_right. (*simpl in H. inversion H.*)
          + crush' false lt_right. (*simpl in H. inversion H.*)
          + crush' false lt_right. (*simpl in H. inversion H.*)
          + crush' false lt_right. (*simpl in H. inversion H.*)
          + constructor. simpl in H; inversion H. destruct H1. destruct H3. dependent destruction H4. dependent destruction H5.
            simpl in H0; inversion H0. destruct H1. destruct H4. dependent destruction H5. dependent destruction H6.
            apply prop2_IH_ghost. assumption. assumption.
          + crush' false lt_right. (*simpl in H. inversion H.*)
          + constructor.
          + crush' false lt_right. (*simpl in H. inversion H.*)
          + constructor. simpl in H; inversion H. destruct H1. destruct H3. dependent destruction H4. dependent destruction H5.
            (* unfold unitt_on_nodes in * *)
            assumption. 
          *)
      }
    + esplit. exists (unitt _ /\1 f0), (f /\1 unitt _). 
      { split.
        - apply same'_trans with (g := (unitt _ <o f) /\1 (f0 <o unitt _)); [auto|].
          apply same'_trans with (g := (f <o unitt _) /\1 (unitt _ <o f0)); [|auto].
          apply same'_trans with (g := f /\1 f0); auto. (* [1] (/\ 2 bif) *)
        - intros; repeat match goal with 
                           | [xtac : nodes (_ /\0 _) |- _] => dep_destruct xtac; clear xtac
                         end; crush' false lt_right.
      }
  - intros; dependent destruction bra_h2.
    + dependent destruction bra_h1.
      * esplit. exists ( bracket_left A B B0 /\1 unitt _ <o bracket_left A (B /\0 B0) C0 ), ( bracket_left (A /\0 B) B0 C0 ).
        { split. 
          - apply same'_sym; eapply same'_trans; [|eapply same'_cat_assoc]; apply same'_bracket_left_5. (* rev [4] (b 5) *)
          - intros; repeat match goal with 
                             | [xtac : nodes (_ /\0 _) |- _] => dep_destruct xtac; clear xtac
                           end; crush' false lt_right.
        }
      * esplit. exists (bracket_left _ _ _), ((unitt _ /\1 f0) /\1 unitt _).
        { split.
          - apply same'_nat. (* rev [2] (b nat) *)
          - intros; repeat match goal with 
                             | [xtac : nodes (_ /\0 _) |- _] => dep_destruct xtac; clear xtac
                           end; crush' false lt_right.
        }
      * esplit. exists  (bracket_left _ _ _), ((unitt _ /\1 unitt _) /\1 f0).
        { split.
          - apply same'_nat. (* rev [2] (b nat) *)
          - intros; repeat match goal with 
                             | [xtac : nodes (_ /\0 _) |- _] => dep_destruct xtac; clear xtac
                           end; crush' false lt_right.
        }            
    + esplit. exists  (f0 /\1 unitt _), (unitt _ /\1 f).
      { split.
        - apply same'_trans with (g := (f0 <o unitt _) /\1 (unitt _ <o f)); [auto|].
          apply same'_trans with (g := (unitt _ <o f0) /\1 (f <o unitt _)); [|auto].
          apply same'_trans with (g := f0 /\1 f); auto. (* rev [1] (/\ 2 bif) *)
        - intros; repeat match goal with 
                           | [xtac : nodes (_ /\0 _) |- _] => dep_destruct xtac; clear xtac
                         end; crush' false lt_right.
      }
    + esplit. set (prop1_IH := fst (projT2 (projT2 (projT2 (IHbra_h1 _ _ bra_h2))))) in |- ; simpl in (type of prop1_IH).
      set (prop2_IH := snd (projT2 (projT2 (projT2 (IHbra_h1 _ _ bra_h2))))) in |- .
      set (h2'_IH := (projT1 (projT2 (projT2 (IHbra_h1 _ _ bra_h2))))) in (type of prop1_IH), (type of prop2_IH).
      set (h1'_IH := (projT1 (projT2 (IHbra_h1 _ _ bra_h2)))) in (type of h2'_IH), (type of prop1_IH), (type of prop2_IH).
      exists (unitt _ /\1 h1'_IH), (unitt _ /\1 h2'_IH).
      set (P_IH := (projT1 (IHbra_h1 _ _ bra_h2))) in (type of h1'_IH), (type of h2'_IH), (type of prop1_IH), (type of prop2_IH) |- *.
      { split.
        - apply same'_trans with (g :=  (unitt _ <o unitt _) /\1 (h1'_IH <o f)); [auto|].
          apply same'_trans with (g := (unitt _ <o unitt _) /\1 (h2'_IH <o f0)); auto. (* (unitt /\ _  induction) *)
        - generalize prop2_IH; clear prop2_IH.
          generalize prop1_IH; clear prop1_IH.
          generalize h2'_IH; clear h2'_IH.
          generalize h1'_IH; clear h1'_IH.
          generalize P_IH; clear P_IH.
          clear bra_h2 IHbra_h1 bra_h1.
          intros; repeat match goal with 
                           | [xtac : nodes (_ /\0 _) |- _] => dep_destruct xtac; clear xtac
                         end; crush' false lt_right.
      }
Defined.
Hint Immediate th200.

(** * First "direct" attempt at semiassociative coherence *)

(* simpl will do these next 4 lemmas, therefore not lacked *)
Lemma th210 : forall Z l,  Z </\0 (letter l) = (Z /\0 (letter l)).
Proof. reflexivity. Defined.
Hint Rewrite th210.

Lemma th220 : forall Z A1 A2, Z </\0 (A1 /\0 A2) = (Z </\0 A1) </\0 A2.
Proof. reflexivity. Defined.
Hint Rewrite th220.

Lemma th221 : forall l, normalize (letter l) = letter l.
Proof. reflexivity. Defined.
Hint Rewrite th221.

Lemma th222 : forall A1 A2, normalize (A1 /\0 A2) = (normalize A1) </\0 A2.
Proof. reflexivity. Defined.
Hint Rewrite th222.

Lemma th223 : forall Y Z (y : arrows Y Z) l, (y </\1 (letter l)) = (y /\1 unitt (letter l)).
Proof. reflexivity. Defined.
Hint Rewrite th223.

Lemma th224 : forall Y Z (y : arrows Y Z) A1 A2, (y </\1 (A1 /\0 A2)) = (((y </\1 A1) </\1 A2) <o bracket_left Y A1 A2).
Proof. reflexivity. Defined.
Hint Rewrite th224.

Lemma th225 : forall l, normalize_arrow (letter l) = (unitt (letter l)).
Proof. reflexivity. Defined.
Hint Rewrite th225.

Lemma th227 : forall A1 A2, normalize_arrow (A1 /\0 A2) = ((normalize_arrow A1) </\1 A2).
Proof. reflexivity. Defined.
Hint Rewrite th227.

Lemma th230 : forall A1 l, normalize_arrow (A1 /\0 letter l) = ((normalize_arrow A1) /\1 (unitt (letter l))).
Proof. reflexivity. Defined.
Hint Rewrite th230.

Lemma th240 : forall A1 A2_1 A2_2, normalize_arrow (A1 /\0 (A2_1 /\0 A2_2)) = (normalize_arrow ((A1 /\0 A2_1) /\0 A2_2) <o bracket_left A1 A2_1 A2_2).
Proof. simpl. reflexivity. Defined.
Hint Rewrite th240. (*useful*)

Lemma th250 : forall N P, arrows_assoc N P -> forall M, normalize_aux M N = normalize_aux M P.
Proof.
  induction 1; crush.
Defined.
Hint Immediate th250.

Lemma th260 : forall N P, arrows_assoc N P -> normalize N = normalize P.
Proof.
  induction 1; crush.
Defined.
Hint Immediate th260.

Lemma normalize_arrow_alt0 : forall A B, arrows_assoc A B -> normal B -> arrows A B.
Proof.
  intros; replace B with (normalize B) by auto.
  replace (normalize B) with (normalize A) by auto.
  exact (normalize_arrow A).
Defined.

Lemma normalize_arrow_alt : forall B A, arrows_assoc B A -> normal B -> arrows A B.
Proof.
  intros; apply normalize_arrow_alt0 with (1 := (rev H)) (2 := H0).
Defined.
(* Hint Immediate normalize_arrow_alt *)


(** BAD LACK ANOTHER TRANSPORT MAP WHICH IS COHERENT, SOME TRANSPORT MAP OTHER THAT [eq_rect].

[[
Fail Scheme Induction for normal Sort Set.

Lemma th270 : forall A (H_normal : normal A), normalize_arrow A ~~~
                                              match (th151 H_normal) in _ = A0 return arrows A A0 -> arrows A (normalize A) with 
                                                | eq_refl => fun f => f 
                                              end (unitt A).
Proof.
  induction H_normal; crush. 
Abort.
]]

**)

(** * This directeness lemma, which is some Newman-style lemma, is really lacked for semiassociative cohence

But this lemma is NOT lacked for associative coherence. The directedness lemma is the semiassociative coherence where the codomain is normal, *)

Lemma th270 : forall A B (f : arrows A B), lengthinr B = lengthinr A -> bracket_left_not_occurs_in f.
Proof.
  intros; assert (Htemp : bracket_left_occurs_in f + bracket_left_not_occurs_in f) by apply th004.
  destruct Htemp; [elimtype Empty_set; eapply th090; eassumption | assumption].
Defined.
Hint Resolve th270.

Lemma th280 : forall A B (f : arrows A B), term_bracket_left f -> bracket_left_occurs_in f.
Proof.
  induction 1; auto.
Defined.
Hint Resolve th280.

(** From earlier coherence.development *)

Lemma development2 : forall A B (f : arrows A B), {dev_f : arrows A B & prod (developed dev_f) (same' f dev_f)}.
Proof.
  intros. split with (projT1 (development f (le_n (length f)))). 
  split. exact (fst (projT2 (development f (le_n (length f))))).
  exact ((snd (snd (projT2 (development f (le_n (length f))))))).
Defined.

Lemma development3 : forall A B (f : arrows A B), {dev_normal_f : arrows A B & prod (developed_normal dev_normal_f) (same' f dev_normal_f)}.
Proof.
  intros. split with (projT1 (developed_normalize (fst (projT2 (development2 f))))).
  split. exact (fst (projT2 (developed_normalize (fst (projT2 (development2 f)))))).
  eapply same'_trans. 2: eapply (same_to_same' (snd (projT2 (developed_normalize (fst (projT2 (development2 f))))))).
  exact (snd (projT2 (development2 f))).
Defined.

Lemma lemma_directedness : forall P, (normal P) -> forall len N, (lengthinr N - lengthinr P <= len) -> forall h k : arrows N P, h ~~~ k.
Proof.
  induction len.
  - intros. cut (bracket_left_not_occurs_in h); cut (bracket_left_not_occurs_in k);
            cut (lengthinr P = lengthinr N); cut (lengthinr P <= lengthinr N); crush.
    destruct (th010 H4) as (-> & ?).
    destruct (th010 H3) as (Htemp & ?); dependent destruction Htemp.
    apply same'_trans with (g := (unitt N)); [apply same_to_same' | apply same'_sym, same_to_same']; assumption.
  - intros. set (H_dev_normal_h := (fst (projT2 (development3 h)))) in |- .
    set (H_same_h := (snd (projT2 (development3 h)))) in |- .
    set (h_dev := (projT1 (development3 h))) in (type of H_dev_normal_h), (type of H_same_h).
    set (H_dev_normal_k := (fst (projT2 (development3 k)))) in |- .
    set (H_same_k := (snd (projT2 (development3 k)))) in |- .
    set (k_dev := (projT1 (development3 k))) in (type of H_dev_normal_k), (type of H_same_k).
    cut (h_dev ~~~ k_dev);
      [ intros; apply same'_trans with (g := h_dev); [|apply same'_trans with (g := k_dev)]; auto |];
    clear H_same_k H_same_h; clearbody H_dev_normal_k; clearbody k_dev; clearbody H_dev_normal_h; clearbody h_dev; clear h k.

    remember h_dev as h_memo in |- ; destruct H_dev_normal_h.
    (* shorter trick than to exfalso the 2 symmetric cases [developed_normal (g <o f) ~~~ unitt] *)
    + cut (bracket_left_not_occurs_in k_dev); [|auto].
      intros Htemp1; destruct (th010 Htemp1) as (Htemp2 & ?); dependent destruction Htemp2; auto.
    + destruct H_dev_normal_k.
      * rewrite <- Heqh_memo.
        cut (bracket_left_not_occurs_in h_memo); [|auto].
        intros Htemp1; destruct (th010 Htemp1) as (Htemp2 & ?); dependent destruction Htemp2; auto.
      * { clear H_dev_normal_h H_dev_normal_k h_memo Heqh_memo.
          set (H_th200 := th200 t t0) in |- .
          set (prop1_H_th200 := fst (projT2 (projT2 (projT2 (H_th200))))) in |- .
          set (prop2_H_th200 := snd (projT2 (projT2 (projT2 (H_th200))))) in |- .
          set (g0' :=  projT1 (projT2 (projT2 (H_th200)))) in (type of prop2_H_th200), (type of prop1_H_th200).
          set (g' :=  projT1 (projT2 (H_th200))) in (type of prop2_H_th200), (type of prop1_H_th200), g0'.
          set (P' := projT1 (H_th200)) in (type of prop2_H_th200), (type of prop1_H_th200), g0', g'.
          
          set (h := normalize_arrow_alt (com_assoc (rev f) g') H) in |- .

          clearbody h;
            clear prop2_H_th200 (* not lacked in this directed lemma *);
            clearbody prop1_H_th200;
            clearbody g0'; clearbody g'; clearbody P'; clear H_th200.

          assert (H_len_f : lengthinr B - lengthinr C <= len);
            [ cut (lengthinr B < lengthinr A); eauto; omega |].
          set (H_same_f_h_g := IHlen _ H_len_f f (h <o g')) in |- .
          assert (H_len_f0 : lengthinr B0 - lengthinr C <= len);
            [ cut (lengthinr B0 < lengthinr A); eauto; omega |].
          set (H_same_f0_h_g0 := IHlen _ H_len_f0 f0 (h <o g0')) in |- .

          clearbody H_same_f0_h_g0; clearbody H_same_f_h_g; clear H_len_f H_len_f0.
          apply same'_trans with (g := ((h <o g') <o g)); [auto|].
          apply same'_trans with (g := (h <o (g' <o g))); [auto|].
          apply same'_trans with (g := ((h <o g0') <o g0)); [|auto].
          apply same'_trans with (g := (h <o (g0' <o g0))); [|auto]. auto.
        }
Defined.
Print lemma_directedness.

(** NOTE: for FIXPOINT, [set] and [let _ in _] instead of [destruct as] because sometimes unfolding and simpl of the fixpoint is done badly when [destruct] is used directly onto the fixpoint hypothesis **)

Lemma lemma_directedness0 : forall B, (normal B) -> forall A (f g : arrows A B), f ~~~ g.
Proof. (* Print Implicit lemma_directedness. *)
  intros; exact (lemma_directedness H (le_n (lengthinr A - lengthinr B)) f g).
Defined.

(** * Now for associative coherence *)

Infix "/\1a" := up_1_assoc (at level 63, right associativity).
Notation "g '<oa' f" := (@com_assoc _ _ _ f g) (at level 65, right associativity). (* reminder '<o' is too high, even higher than = , very bad *)

Inductive same_assoc : forall A B : objects, arrows_assoc A B -> arrows_assoc A B -> Set := 
| same_assoc_refl : forall A B f, @same_assoc A B f f
| same_assoc_trans : forall A B f g h, @same_assoc A B f g -> @same_assoc A B g h -> @same_assoc A B f h
| same_assoc_sym : forall A B f g, @same_assoc A B f g -> @same_assoc A B g f
| same_assoc_cong_com : forall A B C f f0 g g0, @same_assoc A B f f0 -> @same_assoc B C g g0 ->
 @same_assoc A C (g <oa f) (g0 <oa f0)
| same_assoc_cong_up_1 : forall A B A0 B0 f f0 g g0, @same_assoc A B f f0 -> @same_assoc A0 B0 g g0 ->
 @same_assoc (A /\0 A0) (B /\0 B0) (f /\1a g) (f0 /\1a g0)
| same_assoc_cat_left : forall A B, forall f : arrows_assoc A B, @same_assoc A B ( (unitt_assoc B) <oa f ) ( f )
| same_assoc_cat_right : forall A B, forall f : arrows_assoc A B, @same_assoc A B ( f <oa (unitt_assoc A)) ( f )
| same_assoc_cat_assoc : forall A B C D, forall (f : arrows_assoc A B) (g : arrows_assoc B C) (h : arrows_assoc C D), @same_assoc A D ( h <oa (g <oa f)  ) ( (h <oa g) <oa f  )
| same_assoc_bif_up_unit : forall A B, @same_assoc (A /\0 B) (A /\0 B) ((unitt_assoc A) /\1a (unitt_assoc B)) (unitt_assoc (A /\0 B))
| same_assoc_bif_up_com : forall A B C A0 B0 C0, forall (f : arrows_assoc A B) (g : arrows_assoc B C) (f0 : arrows_assoc A0 B0) (g0 : arrows_assoc B0 C0), @same_assoc (A /\0 A0) (C /\0 C0) ( (g <oa f) /\1a (g0 <oa f0) ) ( (g /\1a g0) <oa (f /\1a f0) )
| same_assoc_bracket_left_5 : forall A B C D, 
 @same_assoc (A /\0 (B /\0 (C /\0 D))) ((((A /\0 B) /\0 C) /\0 D))
 ( (bracket_left_assoc (A /\0 B) C D) <oa (bracket_left_assoc A B (C /\0 D)) )
 ( (bracket_left_assoc A B C) /\1a (unitt_assoc D)  <oa (bracket_left_assoc A (B /\0 C) D) <oa (unitt_assoc A) /\1a (bracket_left_assoc B C D) )
| same_assoc_nat : forall A A' f B B' g C C' h, same_assoc (bracket_left_assoc A B C <oa (f /\1a (g /\1a h))) (((f /\1a g) /\1a h) <oa bracket_left_assoc A' B' C')
| same_assoc_bracket_right_bracket_left : forall A B C, same_assoc (bracket_right_assoc A B C <oa bracket_left_assoc A B C) (unitt_assoc (A /\0 (B /\0 C)))
| same_assoc_bracket_left_bracket_right : forall A B C, same_assoc (bracket_left_assoc A B C <oa bracket_right_assoc A B C) (unitt_assoc ((A /\0 B) /\0 C)).

Hint Constructors same_assoc.
Infix "~~~a" := same_assoc (at level 69, no associativity). (* just before = which is at 70 *)

(* OLD, ALTERNATIVE BELOW
Lemma same_assoc_nat_right0 : forall A A' f B B' g C C' h, same_assoc ((f /\1a (g /\1a h)) <oa bracket_right_assoc A' B' C') (bracket_right_assoc A B C <oa ((f /\1a g) /\1a h)).
Proof.
  intros. apply same_assoc_sym.
  apply same_assoc_trans with (g := bracket_right_assoc A B C <oa ((((f /\1a g) /\1a h) <oa bracket_left_assoc A' B' C') <oa bracket_right_assoc A' B' C')); [eauto 11 |].
  apply same_assoc_trans with (g := bracket_right_assoc A B C <oa ((bracket_left_assoc A B C <oa f /\1a g /\1a h) <oa bracket_right_assoc A' B' C')); [| eauto 16]. eauto.
Defined.
Hint Resolve same_assoc_nat_right0.
*)

Lemma th290 : forall A B (f : arrows_assoc A B), (f <oa (rev f) ~~~a (unitt_assoc _)).
Proof.
  induction f; simpl in *; eauto;
  match goal with 
      [ |- (_ <oa _ <oa _) ~~~a _ ] => apply same_assoc_trans with (g :=  f2 <oa (f1 <oa rev f1) <oa rev f2); eauto
  end.
Defined.
Hint Immediate th290.

Lemma th300 : forall A B (f : arrows_assoc A B), ((rev f) <oa f ~~~a (unitt_assoc _)).
Proof.
  intros; pattern f at 1; replace f with (rev (rev f)) by auto; auto 1.
Defined.
Hint Immediate th300.
  
Lemma th310 : forall A B (f g : arrows_assoc A B), f ~~~a g -> rev f ~~~a rev g.
Proof.
  intros.  
  assert (f <oa (rev f) ~~~a (unitt_assoc _)) by auto.
  assert ((rev g) <oa g ~~~a (unitt_assoc _)) by auto.
  apply same_assoc_trans with (g := ((rev g <oa g) <oa rev f)); [eauto |].
  apply same_assoc_trans with (g := ((rev g <oa f) <oa rev f)); [| eauto]. eauto.
Defined.
Hint Resolve th310.

Lemma same_assoc_bracket_right_5 : forall A B C D, bracket_right_assoc A B (C /\0 D) <oa bracket_right_assoc (A /\0 B) C D ~~~a
   (unitt_assoc A /\1a bracket_right_assoc B C D <oa
    bracket_right_assoc A (B /\0 C) D) <oa
   bracket_right_assoc A B C /\1a unitt_assoc D.
Proof.
  intros; apply (th310 (same_assoc_bracket_left_5 A B C D)).
Defined.
Hint Immediate same_assoc_bracket_right_5.

Lemma same_assoc_nat_right : forall A A' f B B' g C C' h, same_assoc ((f /\1a (g /\1a h)) <oa bracket_right_assoc A' B' C') (bracket_right_assoc A B C <oa ((f /\1a g) /\1a h)).
Proof.
  intros; replace f with (rev (rev f)) by auto; replace g with (rev (rev g)) by auto; replace h with (rev (rev h)) by auto.
  apply (th310 (same_assoc_nat (rev f) (rev g) (rev h))).
Defined.
Hint Immediate same_assoc_nat_right.

(** Aborted. Lack better transport map which is coherent, than this [eq_rect]

[[
Lemma lemma_coherence_assoc0 : forall N P (h : arrows_assoc N P), h ~~~a ( (match (th260 h) in _ = NN0 return arrows_assoc NN0 P -> arrows_assoc (normalize N) P with | eq_refl => fun x => x end) (rev (normalize_arrow P)) <oa normalize_arrow N).
Proof.
intros. set (var1 := th260 h). clearbody var1. dependent destruction var1.
Check objects_same. Abort.

Fixpoint arrows_assoc_map (A A0 : objects) (H_objects_same_dom : objects_same A A0) B B0 (H_objects_same_cod : objects_same B B0) {struct H_objects_same_dom} : arrows_assoc A B -> arrows_assoc A0 B0.
Proof. Abort All.
]]

*)

(** ** Some training using semiassociativity *)

Lemma th320 : forall A Y Z (y1 y2 : arrows Y Z), y1 ~~~ y2 -> ((y1 </\1 A) ~~~ (y2 </\1 A)).
Proof.
  induction A; simpl in *; eauto.
Defined.
Hint Resolve th320.

Lemma th330 : forall A Y Z (y1 y2 : arrows Y Z), y1 ~~~a y2 -> ((y1 </\1 A) ~~~a (y2 </\1 A)).
Proof.
  induction A; simpl in *; eauto.
Defined.
Hint Resolve th330.

Lemma th340 : forall A X Y (x : arrows X Y) Z (y : arrows Y Z), (y <o x) </\1 A ~~~ ((y </\1 A) <o (x /\1 unitt A)).
Proof.
  induction A; intros; simpl in *.
  - eauto. (* /\1 bif *)
  - cut (   ((y <o x) </\1 A1 </\1 A2 <o bracket_left X A1 A2) ~~~
   (y </\1 A1 </\1 A2 <o (bracket_left Y A1 A2 <o x /\1 (unitt A1 /\1 unitt A2))) ); [eauto |]. (* /\1 bif unitt, <o assoc *)
    cut (   ((y <o x) </\1 A1 </\1 A2 <o bracket_left X A1 A2) ~~~
   ((y </\1 A1 </\1 A2 <o (x /\1 unitt A1) /\1 unitt A2) <o bracket_left X A1 A2)   ); [eauto |]. (* b nat *)
    cut (   ((y <o x) </\1 A1 </\1 A2) ~~~
   ((y </\1 A1 </\1 A2 <o (x /\1 unitt A1) /\1 unitt A2))   ); [eauto |]. (* cong *)
    cut (   ( (y </\1 A1 <o x /\1 unitt A1) ) </\1 A2 ~~~
   (y </\1 A1 </\1 A2 <o (x /\1 unitt A1) /\1 unitt A2)   ); [eauto |].  (* IHA1 *)
    apply IHA2. (* IHA2 *)
Defined.
Hint Resolve th340.

Lemma th345 : forall A B (f : arrows A B) X Y (x : arrows X Y) Z (y : arrows Y Z), ((y <o x) </\1 B <o unitt X /\1 f) ~~~ ((y </\1 B) <o (x /\1 f)).
Proof.
  intros; apply same'_trans with
          (g := (y </\1 B <o (x /\1 unitt B <o unitt X /\1 f))); [|eauto]. (* /\1 bif *)
  eauto. (*th 345*)
Defined.
Hint Resolve th345.

Fixpoint same'_to_same_assoc A B (f g : arrows A B) (H_same'_f_g : same' f g) {struct H_same'_f_g} : same_assoc f g.
Proof.
  destruct H_same'_f_g.
     constructor 1.
     constructor 2 with (g := g); apply same'_to_same_assoc; assumption.
     constructor 3; apply same'_to_same_assoc; assumption.
     constructor 4; apply same'_to_same_assoc; assumption.
     constructor 5; apply same'_to_same_assoc; assumption.
     constructor 6.
     constructor 7.
     constructor 8.
     constructor 9.
     constructor 10.
     constructor 11.
     constructor 12.
Defined.
Hint Resolve same'_to_same_assoc.
Coercion same'_to_same_assoc : same' >-> same_assoc.


(* BEGIN TRAINING : THIS SEMIASSOCIATIVITY VERSION IS FOR TRAINING ONLY  *)
(* This is some base [unitt] case for [normalize_aux_map] below *)
Fixpoint normalize_aux_map0 X Y (x : arrows X Y) Z (y : arrows Y Z) A {struct A} :
  { y_map : arrows (Y </\0 A) (Z </\0 A) &
                   ( y_map <o (x </\1 A) ) ~~~ ( (y </\1 A) <o (x /\1 unitt A) ) }.
(* begin hide *)
Proof.
    destruct A as [l | A1 A2].
    - simpl. split with (y /\1 unitt (letter l)). simpl. apply same'_refl.
    - simpl. destruct (normalize_aux_map0 _ _ x _ y A1) as [y_map_A1 y_map_A1_prop].
      evar (x_for_A2_dom : objects).
      evar (x_for_A2 : arrows x_for_A2_dom (Y </\0 A1)).
      set (y_for_A2 := y_map_A1).
      destruct (normalize_aux_map0 _ _ x_for_A2 _ y_for_A2 A2) as [y_map_A2 y_map_A2_prop].
      split with y_map_A2.
      cut (  (( y_map_A2 <o x </\1 A1 </\1 A2 ) <o bracket_left X A1 A2) ~~~
   ((y </\1 A1 </\1 A2 <o bracket_left Y A1 A2) <o
   x /\1 unitt (A1 /\0 A2))   ); [eauto |]. (* <oa assoc *)
      cut (   ((y_for_A2 </\1 A2 <o x_for_A2 /\1 unitt A2) <o bracket_left X A1 A2) ~~~
   ((y </\1 A1 </\1 A2 <o bracket_left Y A1 A2) <o
   x /\1 unitt (A1 /\0 A2))   );
        subst x_for_A2_dom; subst x_for_A2; [eauto |]. subst y_for_A2; clear y_map_A2_prop y_map_A2. (* y_map_A2_prop *)
      cut (   (((y_map_A1 <o x </\1 A1) </\1 A2) <o
   bracket_left X A1 A2) ~~~
   ((y </\1 A1 </\1 A2 <o bracket_left Y A1 A2) <o
   x /\1 unitt (A1 /\0 A2)) ); [eauto |]. (* </\1 on <o prearrow th340 *)
      cut (   ((y </\1 A1 <o x /\1 unitt A1) </\1 A2 <o bracket_left X A1 A2) ~~~
   ((y </\1 A1 </\1 A2 <o bracket_left Y A1 A2) <o
   x /\1 unitt (A1 /\0 A2)) ); [eauto |]. clear y_map_A1 y_map_A1_prop. (* y_map_A1_prop *)
      cut (   ((y </\1 A1 </\1 A2 <o (x /\1 unitt A1) /\1 unitt A2) <o bracket_left X A1 A2) ~~~
   ((y </\1 A1 </\1 A2 <o bracket_left Y A1 A2) <o
   x /\1 unitt (A1 /\0 A2)) ); [eauto |]. (* </\1 on <o prearrow th340 *)
      cut (   (y </\1 A1 </\1 A2 <o ((x /\1 unitt A1) /\1 unitt A2 <o
    bracket_left X A1 A2)) ~~~
   (y </\1 A1 </\1 A2 <o (bracket_left Y A1 A2 <o x /\1 unitt (A1 /\0 A2)))    ); [eauto |].
      cut (   ((x /\1 unitt A1) /\1 unitt A2 <o bracket_left X A1 A2) ~~~
   (bracket_left Y A1 A2 <o x /\1 (unitt A1 /\1 unitt A2))    ); [eauto |]. (* cong, /\1 unitt bif *)
      eauto. (* b nat *)
Defined.
(* end hide *)


Fixpoint normalize_aux_map X Y (x : arrows X Y) Z (y : arrows Y Z) A B (f : arrows A B) {struct f} :
  { y_map : arrows (Y </\0 A) (Z </\0 B) &
                   ( y_map <o (x </\1 A) ) ~~~ ( (y </\1 B) <o (x /\1 f) ) }.
(* begin hide *)
Proof.
  destruct f as [A | A B C | A1 B1 A2 B2 f1 f2 | A B C f g ].
  - apply normalize_aux_map0.
  - simpl. destruct (normalize_aux_map0 x y A) as [y_map_A y_map_A_prop].
    destruct (normalize_aux_map0 (x </\1 A) y_map_A B) as [y_map_B y_map_B_prop].
    destruct (normalize_aux_map0 (x </\1 A </\1 B) y_map_B C) as [y_map_C y_map_C_prop].
    split with y_map_C.
    apply same'_trans with
    (g :=    ((y_map_C <o
    (x </\1 A </\1 B </\1 C <o bracket_left (X /\0 A) B C)) <o
    bracket_left X A (B /\0 C))   ); [eauto|]. (* <o assoc *) Show.
    apply same'_trans with
    (g :=    ((  (y_map_C <o x </\1 A </\1 B </\1 C) <o bracket_left (X /\0 A) B C) <o
    bracket_left X A (B /\0 C))     ); [eauto|]. (* <o assoc *)
    apply same'_trans with
    (g :=    ((  (y_map_B </\1 C <o x </\1 A </\1 B /\1 unitt C)  <o bracket_left (X /\0 A) B C) <o
    bracket_left X A (B /\0 C))     ); [eauto|]. clear y_map_C y_map_C_prop. (* y_map_C_prop *)
    apply same'_trans with
    (g :=        ((( (y_map_B <o x </\1 A </\1 B) </\1 C) <o
     bracket_left (X /\0 A) B C) <o bracket_left X A (B /\0 C))      ); [eauto|]. (* th340 *)
    apply same'_trans with
    (g :=        (((   (y_map_A </\1 B <o x </\1 A /\1 unitt B) </\1 C) <o
     bracket_left (X /\0 A) B C) <o bracket_left X A (B /\0 C))      ); [eauto|]. clear y_map_B y_map_B_prop. (* y_map_B_prop *)
    apply same'_trans with
    (g :=        (((   ( (y_map_A <o x </\1 A) </\1 B) </\1 C) <o
     bracket_left (X /\0 A) B C) <o bracket_left X A (B /\0 C))      ); [eauto|]. (* th340 *)
    apply same'_trans with
    (g :=        (((   (   (y </\1 A <o x /\1 unitt A)    </\1 B) </\1 C) <o
     bracket_left (X /\0 A) B C) <o bracket_left X A (B /\0 C))      ); [eauto|]. clear y_map_A y_map_A_prop. (* y_map_A_prop *)
    apply same'_trans with
    (g :=   (((y </\1 A </\1 B <o (x /\1 unitt A) /\1 unitt B ) </\1 C <o bracket_left (X /\0 A) B C) <o
    bracket_left X A (B /\0 C))    ); [eauto|]. (* th340 *)
    apply same'_trans with
    (g :=   (((y </\1 A </\1 B </\1 C <o ((x /\1 unitt A) /\1 unitt B) /\1 unitt C) <o bracket_left (X /\0 A) B C) <o
    bracket_left X A (B /\0 C))    ); [eauto|]. (* th340 *)
    apply same'_trans with
    (g :=   (((y </\1 A </\1 B </\1 C <o bracket_left Y A B /\1 unitt C ) <o
     bracket_left Y (A /\0 B) C) <o x /\1 bracket_left A B C)    ); [|eauto].  (* th340 *)
    apply same'_trans with
    (g :=   ((y </\1 A </\1 B </\1 C <o (bracket_left Y A B /\1 unitt C <o
     bracket_left Y (A /\0 B) C) <o x /\1 bracket_left A B C))    ); [|eauto].  (* <o assoc *) Show.
    apply same'_trans with
    (g :=    ((y </\1 A </\1 B </\1 C <o (((x /\1 unitt A) /\1 unitt B) /\1 unitt C <o
     bracket_left (X /\0 A) B C) <o bracket_left X A (B /\0 C)))   ); [eauto|].  (* <o assoc *) Show.
    apply same'_trans with
    (g :=       (y </\1 A </\1 B </\1 C <o
    (bracket_left Y A B /\1 unitt C <o bracket_left Y (A /\0 B) C) <o
    unitt _ /\1 bracket_left A B C <o x /\1 unitt _)   ); [|eauto 16]. Show. (* /\1 bif *)
    Show.
    apply same'_trans with
    (g :=   (y </\1 A </\1 B </\1 C <o
    ( bracket_left (Y /\0 A) B C <o (x /\1 unitt A) /\1 (unitt B /\1 unitt C) ) <o
    bracket_left X A (B /\0 C))  ) ; [eauto|].   (* b nat *)
    apply same'_trans with
    (g :=   (y </\1 A </\1 B </\1 C <o
    bracket_left (Y /\0 A) B C <o (  bracket_left Y A (B /\0 C) <o x /\1 (unitt A /\1 (unitt B /\1 unitt C))   ) ) ); [eauto|].   (* <o assoc , b nat *)
    apply same'_trans with
    (g :=   (y </\1 A </\1 B </\1 C <o
    ( bracket_left (Y /\0 A) B C <o  bracket_left Y A (B /\0 C) ) <o x /\1 (unitt A /\1 (unitt B /\1 unitt C))  ) ); [eauto|].  (* <o assoc *)
    apply same'_trans with
    (g :=    (y </\1 A </\1 B </\1 C <o
    (  bracket_left Y A B /\1 unitt C <o bracket_left Y (A /\0 B) C <o
    unitt Y /\1 bracket_left A B C ) <o x /\1 unitt (A /\0 B /\0 C))   ); [|eauto 16].  (* <o assoc twice  *)
    cut (   (x /\1 unitt A /\1 unitt B /\1 unitt C) ~~~ (x /\1 unitt (A /\0 B /\0 C))   ); [eauto|]. (* cong *)
    eauto.
  - (* first of two versions: x and f are in arrows and comes from case x/\f of normal th ---- other version: or x and f are in arrows_assoc and _ </\1 A input from arrows_assoc while y and y_map stay in arrows *)
    simpl. destruct (normalize_aux_map _ _ x _ y _ _ f1) as [y_map_f1 y_map_f1_prop].
    evar (x_for_f2_dom : objects).
    evar (x_for_f2 : arrows x_for_f2_dom (Y </\0 A1)).
    set (y_for_f2 := y_map_f1).
    destruct (normalize_aux_map _ _ x_for_f2 _ y_for_f2 _ _ f2) as [y_map_f2 y_map_f2_prop].
    split with y_map_f2.
    cut (   ((y_map_f2 <o x </\1 A1 </\1 A2) <o bracket_left X A1 A2) ~~~
   ((y </\1 B1 </\1 B2 <o bracket_left Y B1 B2) <o x /\1 f1 /\1 f2)   ); [eauto |]. (* <o assoc *)
    cut (   (( y_for_f2 </\1 B2 <o x </\1 A1 /\1 f2) <o bracket_left X A1 A2) ~~~
   ((y </\1 B1 </\1 B2 <o bracket_left Y B1 B2) <o x /\1 f1 /\1 f2)   ); subst x_for_f2_dom x_for_f2; [eauto |]. subst y_for_f2. clear y_map_f2 y_map_f2_prop. (* y_map_f2_prop *)
    Show.
    cut (   (((y_map_f1 <o x </\1 A1) </\1 B2 <o unitt _ /\1 f2) <o bracket_left X A1 A2) ~~~
   ((y </\1 B1 </\1 B2 <o bracket_left Y B1 B2) <o x /\1 f1 /\1 f2)   ); [eauto |]. (* th 345 *)
    cut (   (((y </\1 B1 <o x /\1 f1) </\1 B2 <o unitt (X /\0 A1) /\1 f2) <o
    bracket_left X A1 A2) ~~~
   ((y </\1 B1 </\1 B2 <o bracket_left Y B1 B2) <o x /\1 f1 /\1 f2)   ); [eauto |]. clear y_map_f1 y_map_f1_prop. (* y_map_f1_prop *)
    Show.
    cut (   (((y </\1 B1 </\1 B2 <o (x /\1 f1) /\1 unitt B2) <o unitt (X /\0 A1) /\1 f2) <o
    bracket_left X A1 A2) ~~~
   ((y </\1 B1 </\1 B2 <o bracket_left Y B1 B2) <o x /\1 f1 /\1 f2)   ); [eauto |]. (* th340 *)
    apply same'_trans with
    (g := ((y </\1 B1 </\1 B2 <o (((x /\1 f1) /\1 unitt B2 <o unitt (X /\0 A1) /\1 f2)) <o
    bracket_left X A1 A2)) ); [eauto |].
    apply same'_trans with
    (g := ((y </\1 B1 </\1 B2 <o (((x /\1 f1) /\1 f2)) <o
    bracket_left X A1 A2)) ); [eauto 16 |]. (* /\1 bif *)
    eauto. (* <o assoc , b nat *)
  - simpl. destruct (normalize_aux_map _ _ x _ (unitt Y) _ _ f) as [y_map_f y_map_f_prop].
    (*evar (x_for_g_dom : objects).
    evar (x_for_g : arrows x_for_g_dom Y).*)
    destruct (normalize_aux_map _ _ (unitt Y) _ y _ _ g) as [y_map_g y_map_g_prop].
    split with (y_map_g <o y_map_f).
    apply same'_trans with
    (g :=  (y_map_g <o (y_map_f <o x </\1 A)) ); [eauto|]. (* <o assoc *)
    apply same'_trans with
    (g := (y_map_g <o (unitt Y </\1 B <o x /\1 f))); [eauto|]. (* y_map_f_prop *)
    apply same'_trans with
    (g :=  ((y_map_g <o unitt Y </\1 B) <o x /\1 f)); [eauto|]. (* <o assoc *)
    apply same'_trans with
    (g :=  (y </\1 C <o unitt Y /\1 g) <o x /\1 f); [eauto|]. (* y_map_g_prop *)
    apply same'_trans with
    (g := (y </\1 C <o (unitt Y /\1 g <o x /\1 f))); [eauto|]. (* <o assoc *)
    eauto. (* cong, /\1 bif *)
Defined.
(* end hide *)

(* END TRAINING : THIS SEMIASSOCIATIVITY VERSION WAS FOR TRAINING ONLY *)

(* end hide *)

(** ** RECURSIVE SQUARE *)

(** REWIND, [normalize_aux_map] ABOVE WAS FOR TRAINING, Rewind back to associativity. HERE IS THE USEFUL ONE *)

Reserved Notation "y </\1a A" (at level 57, left associativity).

Fixpoint normalize_aux_arrow_assoc Y Z (y : arrows_assoc Y Z) A : arrows_assoc (Y /\0 A) (Z </\0 A) :=
  match A with
    | letter l => y /\1a unitt_assoc (letter l)
    | A1 /\0 A2 => ((y </\1a A1) </\1a A2) <oa bracket_left_assoc Y A1 A2
  end
where "y </\1a A" := (normalize_aux_arrow_assoc y A).

Fixpoint normalize_arrow_assoc A : arrows_assoc A (normalize A) :=
  match A with
    | letter l => unitt_assoc (letter l)
    | A1 /\0 A2 => (normalize_arrow_assoc A1) </\1a A2
  end.

Inductive directed : forall A B, arrows_assoc A B -> Set :=
| directed_unitt_assoc : forall A : objects, directed (unitt_assoc A)
| directed_bracket_left_assoc : forall A B C : objects, directed (bracket_left_assoc A B C)
| directed_up_1_assoc : forall A B A0 B0 : objects, forall (f : arrows_assoc A B) (f0 : arrows_assoc A0 B0), directed f -> directed f0 -> directed (up_1_assoc f f0)
| directed_com_assoc : forall A B C : objects, forall (f : arrows_assoc A B) (g : arrows_assoc B C), directed f -> directed g -> directed (com_assoc f g).
Hint Constructors directed.

Fixpoint directed_to_semi A B (f : arrows_assoc A B) (dir_f : directed f) : { f_semi : arrows A B & f = f_semi }. (*shall be fixpoint*)
Proof.
  destruct dir_f; simpl in *.
  - split with (unitt _); reflexivity.
  - split with (bracket_left _ _ _); reflexivity.
  - destruct (directed_to_semi _ _ _ dir_f1) as [f1_semi f1_semi_prop].
    destruct (directed_to_semi _ _ _ dir_f2) as [f2_semi f2_semi_prop].
    split with (f1_semi /\1 f2_semi); subst; reflexivity.
  - destruct (directed_to_semi _ _ _ dir_f1) as [f1_semi f1_semi_prop].
    destruct (directed_to_semi _ _ _ dir_f2) as [f2_semi f2_semi_prop].
    split with (f2_semi <o f1_semi); subst; reflexivity.
Defined.
Hint Resolve directed_to_semi.

Fixpoint semi_to_directed A B (f : arrows A B) : directed f.
Proof.
  destruct f; simpl in *.
  constructor 1.
  constructor 2.
  constructor 3; [exact (semi_to_directed _ _ f1) | exact (semi_to_directed _ _ f2)].
  constructor 4; [exact (semi_to_directed _ _ f1) | exact (semi_to_directed _ _ f2)].
Defined.
Hint Immediate semi_to_directed.
Coercion semi_to_directed : arrows >-> directed.

Lemma th350 : forall A Y Z (y : arrows_assoc Y Z), directed y -> directed (y </\1a A).
Proof.
  induction A; simpl in *.
  - intros. constructor; [assumption | constructor].
  - intros. constructor; [constructor|]. apply IHA2. apply IHA1. assumption.
Defined.
Hint Resolve th350.

Lemma th360 : forall A, directed (normalize_arrow_assoc A).
Proof.
  induction A; simpl in *.
  - constructor.
  - auto 2. (*apply th350*)
Defined.
Hint Immediate th360.

Lemma th373 : forall Y Z (y : arrows Y Z) l, (y </\1a (letter l)) = (y /\1a unitt_assoc (letter l)).
Proof. reflexivity. Defined.
Hint Rewrite th373.

Lemma th374 : forall Y Z (y : arrows Y Z) A1 A2, (y </\1a (A1 /\0 A2)) = (((y </\1a A1) </\1a A2) <oa bracket_left Y A1 A2).
Proof. reflexivity. Defined.
Hint Rewrite th374.

Lemma th375 : forall l, normalize_arrow_assoc (letter l) = (unitt_assoc (letter l)).
Proof. reflexivity. Defined.
Hint Rewrite th375.

Lemma th377 : forall A1 A2, normalize_arrow_assoc (A1 /\0 A2) = ((normalize_arrow_assoc A1) </\1a A2).
Proof. reflexivity. Defined.
Hint Rewrite th377.

Lemma th380 : forall A1 l, normalize_arrow_assoc (A1 /\0 letter l) = ((normalize_arrow_assoc A1) /\1a (unitt_assoc (letter l))).
Proof. reflexivity. Defined.
Hint Rewrite th380.

Lemma th390 : forall A1 A2_1 A2_2, normalize_arrow_assoc (A1 /\0 (A2_1 /\0 A2_2)) = (normalize_arrow_assoc ((A1 /\0 A2_1) /\0 A2_2) <oa bracket_left A1 A2_1 A2_2).
Proof. simpl. reflexivity. Defined.
Hint Rewrite th390. (*useful*)

Lemma th430 : forall A Y Z (y1 y2 : arrows_assoc Y Z), y1 ~~~a y2 -> ((y1 </\1a A) ~~~a (y2 </\1a A)).
Proof.
  induction A; simpl in *; eauto.
Defined.
Hint Resolve th430.

Lemma th440 : forall A X Y (x : arrows_assoc X Y) Z (y : arrows_assoc Y Z), (y <oa x) </\1a A ~~~a ((y </\1a A) <oa (x /\1a unitt_assoc A)).
Proof.
  induction A; intros; simpl in *.
  - eauto. (* /\1 bif *)
  - cut (   ((y <oa x) </\1a A1 </\1a A2 <oa bracket_left_assoc X A1 A2) ~~~a
   (y </\1a A1 </\1a A2 <oa (bracket_left_assoc Y A1 A2 <oa x /\1a (unitt_assoc A1 /\1a unitt_assoc A2))) ); [eauto |]. (* /\1a bif unitt_assoc, <oa assoc *)
    cut (   ((y <oa x) </\1a A1 </\1a A2 <oa bracket_left_assoc X A1 A2) ~~~a
   ((y </\1a A1 </\1a A2 <oa (x /\1a unitt_assoc A1) /\1a unitt_assoc A2) <oa bracket_left_assoc X A1 A2)   ); [eauto |]. (* b nat *)
    cut (   ((y <oa x) </\1a A1 </\1a A2) ~~~a
   ((y </\1a A1 </\1a A2 <oa (x /\1a unitt_assoc A1) /\1a unitt_assoc A2))   ); [eauto |]. (* cong *)
    cut (   ( (y </\1a A1 <oa x /\1a unitt_assoc A1) ) </\1a A2 ~~~a
   (y </\1a A1 </\1a A2 <oa (x /\1a unitt_assoc A1) /\1a unitt_assoc A2)   ); [eauto |].  (* IHA1 *)
    apply IHA2. (* IHA2 *)
Defined.
Hint Resolve th440.

Lemma th445 : forall A B (f : arrows_assoc A B) X Y (x : arrows_assoc X Y) Z (y : arrows_assoc Y Z), ((y <oa x) </\1a B <oa unitt_assoc X /\1a f) ~~~a ((y </\1a B) <oa (x /\1a f)).
Proof.
  intros; apply same_assoc_trans with
          (g := (y </\1a B <oa (x /\1a unitt_assoc B <oa unitt_assoc X /\1a f))); [|eauto]. (* /\1a bif *)
  eauto. (*th 345*)
Defined.
Hint Resolve th445.

(** This is the base [unitt_assoc] case of [normalize_aux_map_assoc] below *)

Fixpoint normalize_aux_map_assoc0 X Y (x : arrows_assoc X Y) Z (y : arrows_assoc Y Z) (dir_y : directed y) A {struct A} :
  { y_map : arrows_assoc (Y </\0 A) (Z </\0 A) &
                  prod ( ( y_map <oa (x </\1a A) ) ~~~a ( (y </\1a A) <oa (x /\1a unitt_assoc A) ) ) (directed y_map) }.
Proof.
    destruct A as [l | A1 A2].
    - simpl. split with (y /\1a unitt_assoc (letter l)).
      split. 2: auto.
      simpl. apply same_assoc_refl.
    - simpl. destruct (normalize_aux_map_assoc0 _ _ x _ y dir_y A1) as [y_map_A1 [y_map_A1_prop dir_y_map_A1]].
      evar (x_for_A2_dom : objects).
      evar (x_for_A2 : arrows_assoc x_for_A2_dom (Y </\0 A1)).
      set (y_for_A2 := y_map_A1).
      destruct (normalize_aux_map_assoc0 _ _ x_for_A2 _ y_for_A2 dir_y_map_A1 A2) as [y_map_A2 [y_map_A2_prop dir_y_map_A2]].
      split with y_map_A2.
      split. 2: auto.
      cut (  (( y_map_A2 <oa x </\1a A1 </\1a A2 ) <oa bracket_left_assoc X A1 A2) ~~~a
   ((y </\1a A1 </\1a A2 <oa bracket_left_assoc Y A1 A2) <oa
   x /\1a unitt_assoc (A1 /\0 A2))   ); [eauto |]. (* <oaa assoc *)
      cut (   ((y_for_A2 </\1a A2 <oa x_for_A2 /\1a unitt_assoc A2) <oa bracket_left_assoc X A1 A2) ~~~a
   ((y </\1a A1 </\1a A2 <oa bracket_left_assoc Y A1 A2) <oa
   x /\1a unitt_assoc (A1 /\0 A2))   );
        subst x_for_A2_dom; subst x_for_A2; [eauto |]. subst y_for_A2; clear dir_y_map_A2 y_map_A2_prop y_map_A2. (* y_map_A2_prop *)
      cut (   (((y_map_A1 <oa x </\1a A1) </\1a A2) <oa
   bracket_left_assoc X A1 A2) ~~~a
   ((y </\1a A1 </\1a A2 <oa bracket_left_assoc Y A1 A2) <oa
   x /\1a unitt_assoc (A1 /\0 A2)) ); [eauto |]. (* </\1a on <oa prearrow th340 *)
      cut (   ((y </\1a A1 <oa x /\1a unitt_assoc A1) </\1a A2 <oa bracket_left_assoc X A1 A2) ~~~a
   ((y </\1a A1 </\1a A2 <oa bracket_left_assoc Y A1 A2) <oa
   x /\1a unitt_assoc (A1 /\0 A2)) ); [eauto |]. clear dir_y_map_A1 y_map_A1 y_map_A1_prop. (* y_map_A1_prop *)
      cut (   ((y </\1a A1 </\1a A2 <oa (x /\1a unitt_assoc A1) /\1a unitt_assoc A2) <oa bracket_left_assoc X A1 A2) ~~~a
   ((y </\1a A1 </\1a A2 <oa bracket_left_assoc Y A1 A2) <oa
   x /\1a unitt_assoc (A1 /\0 A2)) ); [eauto |]. (* </\1a on <oa prearrow th340 *)
      cut (   (y </\1a A1 </\1a A2 <oa ((x /\1a unitt_assoc A1) /\1a unitt_assoc A2 <oa
    bracket_left_assoc X A1 A2)) ~~~a
   (y </\1a A1 </\1a A2 <oa (bracket_left_assoc Y A1 A2 <oa x /\1a unitt_assoc (A1 /\0 A2)))    ); [eauto |].
      cut (   ((x /\1a unitt_assoc A1) /\1a unitt_assoc A2 <oa bracket_left_assoc X A1 A2) ~~~a
   (bracket_left_assoc Y A1 A2 <oa x /\1a (unitt_assoc A1 /\1a unitt_assoc A2))    ); [eauto |]. (* cong, /\1a unitt_assoc bif *)
      eauto. (* b nat *)
Defined.

(** THIS IS THE RECURSIVE SQUARE, CODEDUCTIBLE FROM MACLANE PENTAGON *)

Fixpoint normalize_aux_map_assoc X Y (x : arrows_assoc X Y) Z (y : arrows_assoc Y Z) (dir_y : directed y) A B (f : arrows_assoc A B) {struct f} :
  { y_map : arrows_assoc (Y </\0 A) (Z </\0 B) &
                   prod ( ( y_map <oa (x </\1a A) ) ~~~a ( (y </\1a B) <oa (x /\1a f) ) ) (directed y_map) }.
Proof.
  destruct f as [A | A B C | A B C | A1 B1 A2 B2 f1 f2 | A B C f g ].
  - apply normalize_aux_map_assoc0. assumption.
  - simpl. destruct (normalize_aux_map_assoc0 x dir_y A) as [y_map_A [y_map_A_prop dir_y_map_A]].
    destruct (normalize_aux_map_assoc0 (x </\1a A) dir_y_map_A B) as [y_map_B [y_map_B_prop dir_y_map_B]].
    destruct (normalize_aux_map_assoc0 (x </\1a A </\1a B) dir_y_map_B C) as [y_map_C [y_map_C_prop dir_y_map_C]].
    split with y_map_C.
    split. 2: auto.
    apply same_assoc_trans with
    (g :=    ((y_map_C <oa
    (x </\1a A </\1a B </\1a C <oa bracket_left_assoc (X /\0 A) B C)) <oa
    bracket_left_assoc X A (B /\0 C))   ); [eauto|]. (* <oa assoc *) Show.
    apply same_assoc_trans with
    (g :=    ((  (y_map_C <oa x </\1a A </\1a B </\1a C) <oa bracket_left_assoc (X /\0 A) B C) <oa
    bracket_left_assoc X A (B /\0 C))     ); [eauto|]. (* <oa assoc *)
    apply same_assoc_trans with
    (g :=    ((  (y_map_B </\1a C <oa x </\1a A </\1a B /\1a unitt_assoc C)  <oa bracket_left_assoc (X /\0 A) B C) <oa
    bracket_left_assoc X A (B /\0 C))     ); [eauto|]. clear dir_y_map_C y_map_C y_map_C_prop. (* y_map_C_prop *)
    apply same_assoc_trans with
    (g :=        ((( (y_map_B <oa x </\1a A </\1a B) </\1a C) <oa
     bracket_left_assoc (X /\0 A) B C) <oa bracket_left_assoc X A (B /\0 C))      ); [eauto|]. (* th340 *)
    apply same_assoc_trans with
    (g :=        (((   (y_map_A </\1a B <oa x </\1a A /\1a unitt_assoc B) </\1a C) <oa
     bracket_left_assoc (X /\0 A) B C) <oa bracket_left_assoc X A (B /\0 C))      ); [eauto|]. clear dir_y_map_B y_map_B y_map_B_prop. (* y_map_B_prop *)
    apply same_assoc_trans with
    (g :=        (((   ( (y_map_A <oa x </\1a A) </\1a B) </\1a C) <oa
     bracket_left_assoc (X /\0 A) B C) <oa bracket_left_assoc X A (B /\0 C))      ); [eauto|]. (* th340 *)
    apply same_assoc_trans with
    (g :=        (((   (   (y </\1a A <oa x /\1a unitt_assoc A)    </\1a B) </\1a C) <oa
     bracket_left_assoc (X /\0 A) B C) <oa bracket_left_assoc X A (B /\0 C))      ); [eauto|]. clear dir_y_map_A y_map_A y_map_A_prop. (* y_map_A_prop *)
    apply same_assoc_trans with
    (g :=   (((y </\1a A </\1a B <oa (x /\1a unitt_assoc A) /\1a unitt_assoc B ) </\1a C <oa bracket_left_assoc (X /\0 A) B C) <oa
    bracket_left_assoc X A (B /\0 C))    ); [eauto|]. (* th340 *)
    apply same_assoc_trans with
    (g :=   (((y </\1a A </\1a B </\1a C <oa ((x /\1a unitt_assoc A) /\1a unitt_assoc B) /\1a unitt_assoc C) <oa bracket_left_assoc (X /\0 A) B C) <oa
    bracket_left_assoc X A (B /\0 C))    ); [eauto|]. (* th340 *)
    apply same_assoc_trans with
    (g :=   (((y </\1a A </\1a B </\1a C <oa bracket_left_assoc Y A B /\1a unitt_assoc C ) <oa
     bracket_left_assoc Y (A /\0 B) C) <oa x /\1a bracket_left_assoc A B C)    ); [|eauto].  (* th340 *)
    apply same_assoc_trans with
    (g :=   ((y </\1a A </\1a B </\1a C <oa (bracket_left_assoc Y A B /\1a unitt_assoc C <oa
     bracket_left_assoc Y (A /\0 B) C) <oa x /\1a bracket_left_assoc A B C))    ); [|eauto].  (* <oa assoc *) Show.
    apply same_assoc_trans with
    (g :=    ((y </\1a A </\1a B </\1a C <oa (((x /\1a unitt_assoc A) /\1a unitt_assoc B) /\1a unitt_assoc C <oa
     bracket_left_assoc (X /\0 A) B C) <oa bracket_left_assoc X A (B /\0 C)))   ); [eauto|].  (* <oa assoc *) Show.
    apply same_assoc_trans with
    (g :=       (y </\1a A </\1a B </\1a C <oa
    (bracket_left_assoc Y A B /\1a unitt_assoc C <oa bracket_left_assoc Y (A /\0 B) C) <oa
    unitt_assoc _ /\1a bracket_left_assoc A B C <oa x /\1a unitt_assoc _)   ); [|eauto 16]. Show. (* /\1a bif *)
    Show.
    apply same_assoc_trans with
    (g :=   (y </\1a A </\1a B </\1a C <oa
    ( bracket_left_assoc (Y /\0 A) B C <oa (x /\1a unitt_assoc A) /\1a (unitt_assoc B /\1a unitt_assoc C) ) <oa
    bracket_left_assoc X A (B /\0 C))  ) ; [eauto|].   (* b nat *)
    apply same_assoc_trans with
    (g :=   (y </\1a A </\1a B </\1a C <oa
    bracket_left_assoc (Y /\0 A) B C <oa (  bracket_left_assoc Y A (B /\0 C) <oa x /\1a (unitt_assoc A /\1a (unitt_assoc B /\1a unitt_assoc C))   ) ) ); [eauto|].   (* <oa assoc , b nat *)
    apply same_assoc_trans with
    (g :=   (y </\1a A </\1a B </\1a C <oa
    ( bracket_left_assoc (Y /\0 A) B C <oa  bracket_left_assoc Y A (B /\0 C) ) <oa x /\1a (unitt_assoc A /\1a (unitt_assoc B /\1a unitt_assoc C))  ) ); [eauto|].  (* <oa assoc *)
    apply same_assoc_trans with
    (g :=    (y </\1a A </\1a B </\1a C <oa
    (  bracket_left_assoc Y A B /\1a unitt_assoc C <oa bracket_left_assoc Y (A /\0 B) C <oa
    unitt_assoc Y /\1a bracket_left_assoc A B C ) <oa x /\1a unitt_assoc (A /\0 B /\0 C))   ); [|eauto 16].  (* <oa assoc twice  *)
    cut (   (x /\1a unitt_assoc A /\1a unitt_assoc B /\1a unitt_assoc C) ~~~a (x /\1a unitt_assoc (A /\0 B /\0 C))   ); [eauto|]. (* cong *)
    eauto.

  - (* bracket_right_assoc *)
    simpl. destruct (normalize_aux_map_assoc0 x dir_y A) as [y_map_A [y_map_A_prop dir_y_map_A]].
    destruct (normalize_aux_map_assoc0 (x </\1a A) dir_y_map_A B) as [y_map_B [y_map_B_prop dir_y_map_B]].
    destruct (normalize_aux_map_assoc0 (x </\1a A </\1a B) dir_y_map_B C) as [y_map_C [y_map_C_prop dir_y_map_C]].
    split with y_map_C.
    split. 2: auto.
    apply same_assoc_trans with
    (g :=    y_map_C <oa
   (x </\1a A </\1a B </\1a C <oa bracket_left_assoc X A B /\1a unitt_assoc C) <oa
   bracket_left_assoc X (A /\0 B) C    ); [eauto|]. (* th340 *)
    apply same_assoc_trans with
    (g :=    (y_map_C <oa
   x </\1a A </\1a B </\1a C) <oa (bracket_left_assoc X A B /\1a unitt_assoc C <oa
   bracket_left_assoc X (A /\0 B) C)    ); [eauto|]. (* <o assoc *)
    apply same_assoc_trans with
    (g :=    (   y_map_B </\1a C <oa x </\1a A </\1a B /\1a unitt_assoc C   ) <oa (bracket_left_assoc X A B /\1a unitt_assoc C <oa
   bracket_left_assoc X (A /\0 B) C)    ); [eauto|]. clear dir_y_map_C y_map_C_prop y_map_C. (* y_map_C_prop *)
    apply same_assoc_trans with
    (g :=    (   (y_map_B <oa x </\1a A </\1a B) </\1a C   ) <oa (bracket_left_assoc X A B /\1a unitt_assoc C <oa
   bracket_left_assoc X (A /\0 B) C)    ); [eauto|].  (* th340 *)
    apply same_assoc_trans with
    (g :=    (   ( y_map_A </\1a B <oa x </\1a A /\1a unitt_assoc B) </\1a C   ) <oa (bracket_left_assoc X A B /\1a unitt_assoc C <oa
   bracket_left_assoc X (A /\0 B) C)    ); [eauto|]. clear dir_y_map_B y_map_B_prop y_map_B. (* y_map_B_prop *)
    apply same_assoc_trans with
    (g :=    (   ( (y_map_A <oa x </\1a A) </\1a B) </\1a C   ) <oa (bracket_left_assoc X A B /\1a unitt_assoc C <oa
   bracket_left_assoc X (A /\0 B) C)    ); [eauto|]. (* th340 *)
    apply same_assoc_trans with
    (g :=    (   ( ( y </\1a A <oa x /\1a unitt_assoc A ) </\1a B) </\1a C   ) <oa (bracket_left_assoc X A B /\1a unitt_assoc C <oa
   bracket_left_assoc X (A /\0 B) C)    ); [eauto|]. clear dir_y_map_A y_map_A_prop y_map_A. (* y_map_A_prop *)
    apply same_assoc_trans with
    (g :=    (   ( ( y </\1a A </\1a B <oa (x /\1a unitt_assoc A) /\1a unitt_assoc B ) </\1a C   ) <oa (bracket_left_assoc X A B /\1a unitt_assoc C <oa
   bracket_left_assoc X (A /\0 B) C)  )  ); [eauto|]. (* th340 *)
    apply same_assoc_trans with
    (g :=    (   ( ( y </\1a A </\1a B </\1a C <oa ((x /\1a unitt_assoc A) /\1a unitt_assoc B) /\1a unitt_assoc C )  <oa (bracket_left_assoc X A B /\1a unitt_assoc C <oa
   bracket_left_assoc X (A /\0 B) C)))  ); [eauto|]. (* th340 *)
    apply same_assoc_trans with
    (g :=    y </\1a A </\1a B </\1a C <oa
    (  ((x /\1a unitt_assoc A) /\1a unitt_assoc B) /\1a unitt_assoc C <oa
   bracket_left_assoc X A B /\1a unitt_assoc C  )  <oa
   bracket_left_assoc X (A /\0 B) C  ); [eauto|].
    apply same_assoc_trans with
    (g :=    y </\1a A </\1a B </\1a C <oa
    (   (bracket_left_assoc Y A B <oa (x /\1a (unitt_assoc A /\1a unitt_assoc B))) /\1a (unitt_assoc C <oa unitt_assoc C)  )  <oa
   bracket_left_assoc X (A /\0 B) C  ); [eauto 16|].
    apply same_assoc_trans with
    (g :=    y </\1a A </\1a B </\1a C <oa
    (   (bracket_left_assoc Y A B /\1a unitt_assoc C) <oa (x /\1a (unitt_assoc A /\1a unitt_assoc B)) /\1a unitt_assoc C  )  <oa
   bracket_left_assoc X (A /\0 B) C  ); [eauto|].
    apply same_assoc_trans with
    (g :=    y </\1a A </\1a B </\1a C <oa
    (bracket_left_assoc Y A B /\1a unitt_assoc C) <oa ( (x /\1a (unitt_assoc A /\1a unitt_assoc B)) /\1a unitt_assoc C  <oa
   bracket_left_assoc X (A /\0 B) C ) ); [eauto|].
    apply same_assoc_trans with
    (g :=    y </\1a A </\1a B </\1a C <oa
    (bracket_left_assoc Y A B /\1a unitt_assoc C) <oa ( (x /\1a (unitt_assoc (A /\0 B))) /\1a unitt_assoc C  <oa
   bracket_left_assoc X (A /\0 B) C ) ); [eauto 16|].
    apply same_assoc_trans with
    (g :=    y </\1a A </\1a B </\1a C <oa
    (bracket_left_assoc Y A B /\1a unitt_assoc C) <oa 
   bracket_left_assoc Y (A /\0 B) C <oa x /\1a unitt_assoc ((A /\0 B) /\0 C) );
    [ repeat (apply same_assoc_cong_com; try constructor); eauto |].
    apply same_assoc_trans with
    (g :=     ((y </\1a A </\1a B </\1a C <oa bracket_left_assoc (Y /\0 A) B C) <oa
    bracket_left_assoc Y A (B /\0 C)) <oa (unitt_assoc _ <oa x) /\1a (bracket_right_assoc A B C <oa unitt_assoc _)   );
      [| repeat (apply same_assoc_cong_com; try constructor); eauto].
    apply same_assoc_trans with
    (g :=     ((y </\1a A </\1a B </\1a C <oa bracket_left_assoc (Y /\0 A) B C) <oa
    bracket_left_assoc Y A (B /\0 C)) <oa (unitt_assoc _ /\1a bracket_right_assoc A B C) <oa (x /\1a unitt_assoc _)   );
      [| repeat (apply same_assoc_cong_com; try constructor); eauto].
    repeat (apply same_assoc_cong_com; try constructor).
    apply same_assoc_trans with
    (g :=    y </\1a A </\1a B </\1a C <oa
   (bracket_left_assoc Y A B /\1a unitt_assoc C <oa
   bracket_left_assoc Y (A /\0 B) C) <oa x /\1a unitt_assoc ((A /\0 B) /\0 C)   ); [eauto|].  (*<o assoc *)
    apply same_assoc_trans with
    (g :=      (y </\1a A </\1a B </\1a C <oa (   bracket_left_assoc (Y /\0 A) B C <oa
    bracket_left_assoc Y A (B /\0 C) <oa
   unitt_assoc Y /\1a bracket_right_assoc A B C   )  <oa
   x /\1a unitt_assoc ((A /\0 B) /\0 C))    ); [|eauto 16]. (*<o assoc deep *)

    (* make ready for (b 5) *)
    repeat (apply same_assoc_cong_com; try constructor).
    apply same_assoc_trans with
    (g :=    ( bracket_left_assoc (Y /\0 A) B C <oa
   bracket_left_assoc Y A (B /\0 C) ) <oa
   unitt_assoc Y /\1a bracket_right_assoc A B C <oa unitt_assoc _   ); [|eauto].
    apply same_assoc_trans with
    (g :=  (  bracket_left_assoc Y A B /\1a unitt_assoc C <oa
           bracket_left_assoc Y (A /\0 B) C  ) <oa unitt_assoc _ ); [eauto|].
    cut ( unitt_assoc Y /\1a bracket_left_assoc A B C <oa unitt_assoc Y /\1a bracket_right_assoc A B C  ~~~a
          unitt_assoc _ ) ; [|eauto]; intros.
    apply same_assoc_trans with
    (g :=    ( bracket_left_assoc (Y /\0 A) B C <oa
   bracket_left_assoc Y A (B /\0 C) ) <oa
   unitt_assoc Y /\1a bracket_right_assoc A B C <oa ( unitt_assoc Y /\1a bracket_left_assoc A B C <oa unitt_assoc Y /\1a bracket_right_assoc A B C )   ); [|eauto].
    apply same_assoc_trans with
    (g :=  (  bracket_left_assoc Y A B /\1a unitt_assoc C <oa
           bracket_left_assoc Y (A /\0 B) C  ) <oa ( unitt_assoc Y /\1a bracket_left_assoc A B C <oa unitt_assoc Y /\1a bracket_right_assoc A B C ) ); [eauto|].
    clear H.
    apply same_assoc_trans with
    (g :=  (  (  bracket_left_assoc Y A B /\1a unitt_assoc C <oa
           bracket_left_assoc Y (A /\0 B) C  ) <oa unitt_assoc Y /\1a bracket_left_assoc A B C )  <oa unitt_assoc Y /\1a bracket_right_assoc A B C ); [eauto|].
    apply same_assoc_trans with
    (g :=    ( bracket_left_assoc (Y /\0 A) B C <oa
   bracket_left_assoc Y A (B /\0 C) ) <oa
   ( unitt_assoc Y /\1a bracket_right_assoc A B C <oa unitt_assoc Y /\1a bracket_left_assoc A B C ) <oa unitt_assoc Y /\1a bracket_right_assoc A B C   ); [|eauto].
    cut (  (unitt_assoc Y /\1a bracket_right_assoc A B C <oa
    unitt_assoc Y /\1a bracket_left_assoc A B C)  ~~~a unitt_assoc _); [|eauto]; intros.
    apply same_assoc_trans with
    (g :=    ( bracket_left_assoc (Y /\0 A) B C <oa
   bracket_left_assoc Y A (B /\0 C) ) <oa
   ( unitt_assoc _ ) <oa unitt_assoc Y /\1a bracket_right_assoc A B C   ); [|eauto].
    clear H.
    apply same_assoc_trans with
    (g :=    ( bracket_left_assoc (Y /\0 A) B C <oa
   bracket_left_assoc Y A (B /\0 C) ) <oa
   unitt_assoc Y /\1a bracket_right_assoc A B C   ); [|eauto].
    apply same_assoc_cong_com; [constructor|].
    eauto. (* (b 5) *)

  - (* second of two versions: other version: x and f are in arrows and comes from case x/\f of normal th ---- this version: or x and f are in arrows_assoc and _ </\1a A input from arrows_assoc while y and y_map stay in arrows *)
    simpl. destruct (normalize_aux_map_assoc _ _ x _ y dir_y _ _ f1) as [y_map_f1 [y_map_f1_prop dir_y_map_f1]].
    evar (x_for_f2_dom : objects).
    evar (x_for_f2 : arrows_assoc x_for_f2_dom (Y </\0 A1)).
    set (y_for_f2 := y_map_f1).
    destruct (normalize_aux_map_assoc _ _ x_for_f2 _ y_for_f2 dir_y_map_f1 _ _ f2) as [y_map_f2 [y_map_f2_prop dir_y_map_f2]].
    split with y_map_f2.
    split. 2: assumption.
    cut (   ((y_map_f2 <oa x </\1a A1 </\1a A2) <oa bracket_left_assoc X A1 A2) ~~~a
   ((y </\1a B1 </\1a B2 <oa bracket_left_assoc Y B1 B2) <oa x /\1a f1 /\1a f2)   ); [eauto |]. (* <oa assoc *)
    cut (   (( y_for_f2 </\1a B2 <oa x </\1a A1 /\1a f2) <oa bracket_left_assoc X A1 A2) ~~~a
   ((y </\1a B1 </\1a B2 <oa bracket_left_assoc Y B1 B2) <oa x /\1a f1 /\1a f2)   ); subst x_for_f2_dom x_for_f2; [eauto 16|]. subst y_for_f2. clear dir_y_map_f2 y_map_f2 y_map_f2_prop. (* y_map_f2_prop *)
    Show.
    cut (   (((y_map_f1 <oa x </\1a A1) </\1a B2 <oa unitt_assoc _ /\1a f2) <oa bracket_left_assoc X A1 A2) ~~~a
   ((y </\1a B1 </\1a B2 <oa bracket_left_assoc Y B1 B2) <oa x /\1a f1 /\1a f2)   ); [eauto |]. (* th 345 *)
    cut (   (((y </\1a B1 <oa x /\1a f1) </\1a B2 <oa unitt_assoc (X /\0 A1) /\1a f2) <oa
    bracket_left_assoc X A1 A2) ~~~a
   ((y </\1a B1 </\1a B2 <oa bracket_left_assoc Y B1 B2) <oa x /\1a f1 /\1a f2)   ); [eauto |]. clear dir_y_map_f1 y_map_f1 y_map_f1_prop. (* y_map_f1_prop *)
    Show.
    cut (   (((y </\1a B1 </\1a B2 <oa (x /\1a f1) /\1a unitt_assoc B2) <oa unitt_assoc (X /\0 A1) /\1a f2) <oa
    bracket_left_assoc X A1 A2) ~~~a
   ((y </\1a B1 </\1a B2 <oa bracket_left_assoc Y B1 B2) <oa x /\1a f1 /\1a f2)   ); [eauto |]. (* th340 *)
    apply same_assoc_trans with
    (g := ((y </\1a B1 </\1a B2 <oa (((x /\1a f1) /\1a unitt_assoc B2 <oa unitt_assoc (X /\0 A1) /\1a f2)) <oa
    bracket_left_assoc X A1 A2)) ); [eauto |].
    apply same_assoc_trans with
    (g := ((y </\1a B1 </\1a B2 <oa (((x /\1a f1) /\1a f2)) <oa
    bracket_left_assoc X A1 A2)) ); [eauto 16 |]. (* /\1a bif *)
    eauto. (* <oa assoc , b nat *)
  - simpl. edestruct normalize_aux_map_assoc with (x:=x) (y:=(unitt_assoc Y)) (f:=f) as [y_map_f [y_map_f_prop dir_y_map_f]]; [constructor|].
    (* \\\ *)
    destruct (normalize_aux_map_assoc _ _ (unitt_assoc Y) _ y dir_y _ _ g) as [y_map_g [y_map_g_prop dir_y_map_g]].
    split with (y_map_g <oa y_map_f).
    split. 2: constructor; assumption.
    apply same_assoc_trans with
    (g :=  (y_map_g <oa (y_map_f <oa x </\1a A)) ); [eauto|]. (* <oa assoc *)
    apply same_assoc_trans with
    (g := (y_map_g <oa (unitt_assoc Y </\1a B <oa x /\1a f))); [eauto|]. (* y_map_f_prop *)
    apply same_assoc_trans with
    (g :=  ((y_map_g <oa unitt_assoc Y </\1a B) <oa x /\1a f)); [eauto|]. (* <oa assoc *)
    apply same_assoc_trans with
    (g :=  (y </\1a C <oa unitt_assoc Y /\1a g) <oa x /\1a f); [eauto|]. (* y_map_g_prop *)
    apply same_assoc_trans with
    (g := (y </\1a C <oa (unitt_assoc Y /\1a g <oa x /\1a f))); [eauto|]. (* <oa assoc *)
    eauto. (* cong, /\1a bif *)
Defined.

Fixpoint normalize_map_assoc A B (f : arrows_assoc A B) {struct f} :
  { y_map : arrows_assoc (normalize A) (normalize B) &
                         prod ( ( y_map <oa normalize_arrow_assoc A ) ~~~a ( normalize_arrow_assoc B <oa f ) ) (directed y_map) }.
Proof.
  destruct f as [A | A B C | A B C | A1 B1 A2 B2 f1 f2 | A B C f g ].
  - simpl. split with (unitt_assoc (normalize A)). simpl.
    split. 2: constructor.
    eauto.
  - simpl. split with (unitt_assoc (normalize A </\0 B </\0 C)).
    split. 2: constructor.
    eauto.
  - simpl. split with (unitt_assoc (normalize A </\0 B </\0 C)).
    split. 2: constructor.
    eauto 16. (* <oa unitt, <oa assoc , b left right *)
  - (* CASE /\1 : [normalize_aux_map_assoc] IS USED HERE ONLY *)
    simpl.
    destruct (normalize_map_assoc _ _ f1) as [y_map_f1 [y_map_f1_prop dir_y_map_f1]].
    destruct (normalize_aux_map_assoc (normalize_arrow_assoc A1) (*y_map_f1*) dir_y_map_f1 f2) as [y_map_f2 [y_map_f2_prop dir_y_map_f2]].
    split with y_map_f2.
    split. 2: assumption.
    apply same_assoc_trans with
    (g :=   y_map_f1 </\1a B2 <oa normalize_arrow_assoc A1 /\1a f2  ); [eauto|]. (* y_map_f1 *)
    apply same_assoc_trans with
    (g :=   (y_map_f1 </\1a B2 <oa normalize_arrow_assoc A1 /\1a unitt_assoc _) <oa unitt_assoc _ /\1a f2    ); [eauto|]. (* /\1 bif , <o assoc *)
    apply same_assoc_trans with
    (g :=   ((y_map_f1 <oa normalize_arrow_assoc A1) </\1a B2) <oa unitt_assoc _ /\1a f2    ); [eauto|]. (* th340 *)
    apply same_assoc_trans with
    (g :=   ((   normalize_arrow_assoc B1 <oa f1    ) </\1a B2) <oa unitt_assoc _ /\1a f2    ); [eauto|]. (* y_map_f2 *)
    apply same_assoc_trans with
    (g :=   (   normalize_arrow_assoc B1 </\1a B2  <oa f1 /\1a unitt_assoc B2    ) <oa unitt_assoc _ /\1a f2    ); [eauto|]. (* th340 *)
    eauto.  (* <o assoc , /\1a bif *)
  - set (y_map_f_prop := fst (projT2 (normalize_map_assoc _ _ f))) in |- ; simpl in y_map_f_prop.
    set (dir_y_map_f := snd (projT2 (normalize_map_assoc _ _ f))) in |- ; simpl in dir_y_map_f.
    set (y_map_f := (projT1 (normalize_map_assoc _ _ f))) in y_map_f_prop , dir_y_map_f.
    set (y_map_g_prop := fst (projT2 (normalize_map_assoc _ _ g))) in |- ; simpl in y_map_g_prop.
    set (dir_y_map_g := snd (projT2 (normalize_map_assoc _ _ g))) in |- ; simpl in dir_y_map_g.
    set (y_map_g := (projT1 (normalize_map_assoc _ _ g))) in y_map_g_prop , dir_y_map_g. 
    (* BUG COQ BUG ????????
    [set] INSTEAD OF [destruct] SO THAT THE FIXPOINT [unfold] WELL FOR COMPUTATION AS IN [th450] BELOW
    destruct (normalize_map_assoc _ _ f) as [y_map_f [y_map_f_prop dir_y_map_f]].
    destruct (normalize_map_assoc _ _ g) as [y_map_g [y_map_g_prop dir_y_map_g]]. *)
    split with (y_map_g <oa y_map_f).
    split. 2: constructor; assumption. 
    apply same_assoc_trans with
    (g := y_map_g <oa (y_map_f <oa normalize_arrow_assoc A)); [eauto|].
    apply same_assoc_trans with
    (g := y_map_g <oa ( normalize_arrow_assoc B <oa f )); [eauto|].
    apply same_assoc_trans with
    (g := ( y_map_g <oa normalize_arrow_assoc B ) <oa f ); [eauto|].
    apply same_assoc_trans with
    (g := (  normalize_arrow_assoc C <oa g ) <oa f ); [eauto|].
    eauto. (* <o assoc *)
Defined.

(* OLD NOT LACKED, because we dont do development for assoc
Lemma th450 : forall A B C (f : arrows_assoc A B) (g : arrows_assoc B C),
                projT1 (normalize_map_assoc (g <oa f)) = projT1 (normalize_map_assoc g) <oa projT1 (normalize_map_assoc f).
Proof.
  simpl. reflexivity.
Defined.
Hint Rewrite th450.
*)

(** BEGIN DEVELOPMENT_NORMAL_ASSOC *)

(** None. *)

(** END DEVELOPMENT_NORMAL_ASSOC *)


(** ** Associative coherence or the structure of endomorphisms in the semiassociative category *)

Lemma th520 : forall A B C, projT1 (normalize_map_assoc (bracket_left_assoc A B C)) ~~~a unitt_assoc _ .
Proof.
  intros; simpl. apply same_assoc_refl.
Defined.

Lemma th530 : forall A (f : arrows A A), f ~~~ unitt A.
Proof.
  intros.
  assert (bracket_left_not_occurs_in f) by auto.
  destruct (th010 H) as (Htemp1 & ?); dependent destruction Htemp1.
  auto 2.
Defined.
Hint Immediate th530.

Lemma th540 : forall A (f g : arrows A A), f ~~~ g.
Proof.
  eauto.
Defined.
Hint Immediate th540.

(** this lemma critically uses the structure of the semi_assoc endomorphisms which are all same as unitt *)
Lemma th550 : forall A B (f g : arrows_assoc A B), projT1 (normalize_map_assoc f) ~~~a projT1 (normalize_map_assoc g).
Proof.
  intros; set (normalize_map_assoc_f_dir := snd (projT2 (normalize_map_assoc f))).
  destruct (directed_to_semi normalize_map_assoc_f_dir) as [normalize_map_assoc_f_semi normalize_map_assoc_f_semi_prop].
  rewrite normalize_map_assoc_f_semi_prop.
  set (normalize_map_assoc_g_dir := snd (projT2 (normalize_map_assoc g))).
  destruct (directed_to_semi normalize_map_assoc_g_dir) as [normalize_map_assoc_g_semi normalize_map_assoc_g_semi_prop].
  rewrite normalize_map_assoc_g_semi_prop.
  apply same'_to_same_assoc.
  clear - f.
  assert (Htemp: (normalize A) = (normalize B)) by auto 1.
  clear - Htemp.
  revert normalize_map_assoc_f_semi normalize_map_assoc_g_semi.
  rewrite Htemp; clear Htemp.
  auto 1.
Defined.
Hint Immediate th550.

Lemma lemma_coherence_assoc : forall A B (f g : arrows_assoc A B), f ~~~a g.
Proof.
  intros; set (normalize_map_assoc_f_prop := fst (projT2 (normalize_map_assoc f))) in |- .
  set (normalize_map_assoc_g_prop := fst (projT2 (normalize_map_assoc g))) in |- .
  assert (normalize_map_assoc_f_g_prop : projT1 (normalize_map_assoc f) ~~~a projT1 (normalize_map_assoc g)) by auto 1.
  cut (  normalize_arrow_assoc B <oa f  ~~~a normalize_arrow_assoc B <oa g  ).
  clear; intros.
  apply same_assoc_trans with
  (g := (rev (normalize_arrow_assoc B) <oa normalize_arrow_assoc B) <oa f); [eauto|].
  apply same_assoc_trans with
  (g := (rev (normalize_arrow_assoc B) <oa normalize_arrow_assoc B) <oa g); [|eauto].
  eauto.

  eauto.
Defined.
Hint Immediate lemma_coherence_assoc.

(** * Semiassociative coherence  *)

(** This [th560] is the meta technicality, which uses associative coherence, which was lacked before we could progress from the directedlemma, which is semiassociative coherence where the codomain is normal, to all the semiassociative coherence. *)

Lemma th560 : forall A B (f g : arrows_assoc A B), forall x : nodes A, f x = g x.
Proof.
  intros until g. cut (f ~~~a g); [|auto 1].
  induction 1; intros;
  repeat match goal with 
           | [xtac : nodes (_ /\0 _) |- _] => dep_destruct xtac; clear xtac
         end; crush.
Defined. Hint Immediate th560.

Lemma lemma_coherence0 : forall P len N, (lengthinr N - lengthinr P <= len) -> forall h k : arrows N P, h ~~~ k.
Proof.
  induction len.
  - intros. cut (bracket_left_not_occurs_in h); cut (bracket_left_not_occurs_in k);
            cut (lengthinr P = lengthinr N); cut (lengthinr P <= lengthinr N); crush.
    destruct (th010 H3) as (-> & ?).
    destruct (th010 H2) as (Htemp & ?); dependent destruction Htemp.
    apply same'_trans with (g := (unitt N)); [apply same_to_same' | apply same'_sym, same_to_same']; assumption.
  - intros. set (H_dev_normal_h := (fst (projT2 (development3 h)))) in |- .
    set (H_same_h := (snd (projT2 (development3 h)))) in |- .
    set (h_dev := (projT1 (development3 h))) in (type of H_dev_normal_h), (type of H_same_h).
    set (H_dev_normal_k := (fst (projT2 (development3 k)))) in |- .
    set (H_same_k := (snd (projT2 (development3 k)))) in |- .
    set (k_dev := (projT1 (development3 k))) in (type of H_dev_normal_k), (type of H_same_k).
    cut (h_dev ~~~ k_dev);
      [ intros; apply same'_trans with (g := h_dev); [|apply same'_trans with (g := k_dev)]; auto |];
    clear H_same_k H_same_h; clearbody H_dev_normal_k; clearbody k_dev; clearbody H_dev_normal_h; clearbody h_dev; clear h k.

    remember h_dev as h_memo in |- ; destruct H_dev_normal_h.
    (* shorter trick than to exfalso the 2 symmetric cases [developed_normal (g <o f) ~~~ unitt] *)
    + cut (bracket_left_not_occurs_in k_dev); [|auto].
      intros Htemp1; destruct (th010 Htemp1) as (Htemp2 & ?); dependent destruction Htemp2; auto.
    + destruct H_dev_normal_k.
      * rewrite <- Heqh_memo.
        cut (bracket_left_not_occurs_in h_memo); [|auto].
        intros Htemp1; destruct (th010 Htemp1) as (Htemp2 & ?); dependent destruction Htemp2; auto.
      * { clear H_dev_normal_h H_dev_normal_k h_memo Heqh_memo.
          set (H_th200 := th200 t t0) in |- .
          set (prop1_H_th200 := fst (projT2 (projT2 (projT2 (H_th200))))) in |- .
          set (prop2_H_th200 := snd (projT2 (projT2 (projT2 (H_th200))))) in |- .
          set (g0' :=  projT1 (projT2 (projT2 (H_th200)))) in (type of prop2_H_th200), (type of prop1_H_th200).
          set (g' :=  projT1 (projT2 (H_th200))) in (type of prop2_H_th200), (type of prop1_H_th200), g0'.
          set (P' := projT1 (H_th200)) in (type of prop2_H_th200), (type of prop1_H_th200), g0', g'.
          (* clear prop2_H_th200 (* lacked in this nondirected lemma *) *)
          clearbody prop2_H_th200;
          clearbody prop1_H_th200;
            clearbody g0'; clearbody g'; clearbody P'; clear H_th200.

          (* BEGIN: DIFFERENCE FROM DIRECTNESS LEMMA *)
          assert (H_cumul_lt_right: forall u v : nodes C, lt_right u v -> lt_right ((g' <oa (rev f)) u) ((g' <oa (rev f)) v) ).
          {  clear - prop2_H_th200 f0. simpl. intros.
             apply prop2_H_th200.
             - replace ((rev g') (g' ((rev f) u))) with ((rev f) u) by auto 1;
               replace ((rev g') (g' ((rev f) v))) with ((rev f) v) by auto 1.
               replace u with (f ((rev f) u)) in H by auto;
                 replace v with (f ((rev f) v)) in H by auto.
               eapply th001; eassumption.
             - replace ((rev g0') (g' ((rev f) u))) with ( ((rev g0') <oa g' <oa (rev f)) u ) by (simpl; auto 1);
               replace ((rev g0') (g' ((rev f) v))) with ( ((rev g0') <oa g' <oa (rev f)) v ) by (simpl; auto 1).
               replace ( ((rev g0') <oa g' <oa (rev f)) u ) with ((rev f0) u) by apply th560. (* th560 here *)
               replace ( ((rev g0') <oa g' <oa (rev f)) v ) with ((rev f0) v) by apply th560. (* th560 here *)
               replace u with (f0 ((rev f0) u)) in H by auto;
                 replace v with (f0 ((rev f0) v)) in H by auto.
               eapply th001; eassumption.               
          }

          set (h := lemma_completeness (g' <oa rev f) H_cumul_lt_right : arrows P' C).
          clearbody h.
          (* END: DIFFERENCE FROM DIRECTNEDD LEMMA *)

          assert (H_len_f : lengthinr B - lengthinr C <= len);
            [ cut (lengthinr B < lengthinr A); eauto; omega |].
          set (H_same_f_h_g := IHlen _ H_len_f f (h <o g')) in |- .
          assert (H_len_f0 : lengthinr B0 - lengthinr C <= len);
            [ cut (lengthinr B0 < lengthinr A); eauto; omega |].
          set (H_same_f0_h_g0 := IHlen _ H_len_f0 f0 (h <o g0')) in |- .

          clearbody H_same_f0_h_g0; clearbody H_same_f_h_g; clear H_len_f H_len_f0.
          apply same'_trans with (g := ((h <o g') <o g)); [auto|].
          apply same'_trans with (g := (h <o (g' <o g))); [auto|].
          apply same'_trans with (g := ((h <o g0') <o g0)); [|auto].
          apply same'_trans with (g := (h <o (g0' <o g0))); [|auto]. auto.
        }
Defined.

Lemma lemma_coherence : forall A B (f g : arrows A B), f ~~~ g.
Proof.
  intros; exact (@lemma_coherence0 B _ A (le_n (lengthinr A - lengthinr B)) f g).
Defined.
