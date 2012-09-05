Require Import Setoid. 
Notation lex x y := 
  (match x with 
    | Eq => y
    | c => c
  end). 

Section t. 
  Variable A B: Type. 
  Variable f : A -> A -> comparison.
  Variable g : B -> B -> comparison.
  Hypothesis Hf_sym: forall x y,  f x y = CompOpp (f y x). 
  Hypothesis Hf_trans:forall c x y z,  f x y = c -> f y z = c -> f x z = c. 
  Hypothesis Hg_sym: forall x y,  g x y = CompOpp (g y x). 
  Hypothesis Hg_trans:forall c x y z,  g x y = c -> g y z = c -> g x z = c. 

  Hint Resolve Hf_sym Hf_trans Hg_sym Hg_trans : lex. 
  Lemma lex_sym x1 x2 y1 y2: lex (f x1 x2) (g y1 y2) = CompOpp (lex (f x2 x1) (g y2 y1)).
  Proof. 
    repeat match goal with 
               |- context [f ?x ?y] => case_eq (f x y); intros ?
             | |- context [f ?x ?y] => case_eq (g x y); intros ?
             | H : f ?x ?y = _, H' : f ?y ?x = _ |- _ => 
               rewrite Hf_sym, H' in H; simpl in H; clear H'; try discriminate
           end; simpl; try eauto with lex. 
  Qed.

  Lemma CompOpp_move x y : CompOpp x = y <-> x = CompOpp y. 
  Admitted.
  
  Lemma Hf_sym' c x y : f x y = CompOpp c -> f y x = c. 
  Proof.   
    intros. rewrite Hf_sym. rewrite CompOpp_move. assumption.
  Qed. 

  Hint Resolve Hf_sym' : lex. 

  Lemma lex_trans c x1 x2 x3 y1 y2 y3: 
    lex (f x1 x2) (g y1 y2) = c -> 
    lex (f x2 x3) (g y2 y3) = c -> 
    lex (f x1 x3) (g y1 y3) = c.
  Proof. 
    Ltac finish :=
      repeat match goal with 
               | H : ?x = ?y, H' : ?x = ?z |- _ => constr_eq y z; clear H'
               | H : ?x = ?y, H' : ?x = ?z |- _ => 
                 rewrite H in H'; discriminate
             end; simpl; try eauto with lex. 

    repeat match goal with 
               |- context [f ?x ?y] => case_eq (f x y); intros ?
             | |- context [f ?x ?y] => case_eq (g x y); intros ?
             | H : f ?x ?y = _, H' : f ?y ?x = _ |- _ => 
               rewrite Hf_sym, H' in H; simpl in H; clear H'; try discriminate
             | H : f ?x ?y = _, H' : f ?y ?z = _ |- _ => 
               pose proof (Hf_trans _ _ _ _ H H'); clear H H'
           end; finish. 

    assert (f x2 x3 = Eq) by eauto with lex; finish. 
    assert (f x1 x2 = Gt) by eauto with lex; finish. 
    assert (f x2 x3 = Eq) by eauto with lex; finish. 
    assert (f x1 x2 = Lt) by eauto with lex; finish. 
    assert (f x1 x2 = Eq) by eauto with lex; finish. 
    assert (f x2 x3 = Gt) by eauto with lex; finish. 
    congruence. 
    assert (f x1 x2 = Eq) by eauto with lex; finish. 
    assert (f x2 x3 = Lt) by eauto with lex; finish. 
    congruence. 
  Qed. 
End t. 
