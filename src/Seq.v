(** A few results on lists.   *)

Section t. 
Require List.
Context {A : Type}.
Section In. 

  Inductive In (a: A): list A -> Type :=
    | In_cons : forall tl, In a (a::tl)
    | In_skip : forall hd tl, In a tl -> In a (hd::tl). 

  Hint Constructors In. 
  Lemma In_app a l l' : In a (l ++ l') -> 
                      (In a l) + (In a l').  
  Proof. 
    induction l; simpl. 
    tauto.
    intros H. inversion H; subst. left. apply In_cons.
    apply IHl in X. destruct X. 
    left; apply In_skip. auto. auto. 
  Qed. 

  Lemma In_nil : forall a, In a nil -> False. 
  Proof. 
    intros a H. inversion H. 
  Qed. 
  
  Lemma In_cons_inversion : forall a hd tl,  
                              In a (hd :: tl) -> (a = hd) + In a tl. 
  Proof. 
    intros a hd tl H. 
    inversion H; subst; tauto. 
  Qed. 
End In. 
End t. 