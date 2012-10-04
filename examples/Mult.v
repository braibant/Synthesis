Require Import Common DList Core Front. 
    
Require ZArith. Open Scope Z_scope.

Section t. 
  Variable W : nat. 
  Notation NUM := (Tint W). 
  Notation STATUS := (Tfin 3). 

  Definition Phi : state := (Treg NUM :: Treg NUM  :: Treg NUM ::  nil)%list. 
    
  Notation N := (var_0 : var Phi (Treg NUM)).
  Notation M := (var_S (var_0) : var Phi (Treg NUM)).  
  Notation R := (var_S (var_S (var_0)) : var Phi (Treg NUM)).  
  
  Notation "'If' c 'then' b1 'else' b2 " := 
  (OrElse _ _ _ (WHEN (c)%expr ; b1)%action b2) 
    (no associativity, at level 200, c,b1,b2 at level 200). 
  
  Definition mult : Action Phi Tunit. intros V. 
  refine ( do n <- ! N; 
           do m <- ! M; 
           do acc <- ! R;
           ( 
           If (m = #i 0) 
           then
                ret (#Ctt)              
           else 
             (               
               do _ <- M ::= (m - (#i 1)) ;
               do _ <- R ::= (acc + n);
               ret (#Ctt))
           ))%action. 
  Defined.
  
  Section correct.
    Definition S := (Word.T W * Word.T W * Word.T W)%type. 
    Require Import ZArith. 
    Inductive trans : relation S :=
    | trans_nop : forall acc n, 
                    trans (n,Word.repr _ 0,acc) (n,Word.repr _ 0,acc)
    | trans_add : forall acc n m,  
                    (0 < Word.unsigned m)%Z ->
                    trans (n,m,acc) (n, Word.sub m (Word.repr _  1), Word.add acc n)%Z. 

    Definition EQ (s : S) (s' : eval_state Phi) : Prop. 
    refine (
        match s with 
            | (n,m,acc) => 
                let n' := DList.hd s' in 
                let m' := DList.hd (DList.tl s') in 
                let acc' := DList.hd (DList.tl (DList.tl s')) in 
                  n = n' /\ m = m'/\ acc = acc'
        end). 
    Defined. 
    Notation "s ~~> t" := (trans s t) (no associativity, at level 80). 
    Notation "s == s'" := (EQ s s') (no associativity, at level 81). 

    Lemma simulation s s' : 
      s == s'->
      forall t, s  ~~> t -> 
           t == Next Phi s' mult. 
    Proof. 
      intros. unfold Next, Eval. unfold Phi in s'.
      repeat DList.inversion. simpl. 
      
      cbv [Sem.Dyn.Bind Sem.Dyn.OrElse Sem.Dyn.Return Sem.Dyn.Retry DList.tl DList.hd].
      Ltac d :=        
      let rec d x :=
          match x with 
            | context [match ?x with _ => _ end] =>
                first [d x | case_eq x; intros]
            | context [if ?x then _ else _] =>
                first [d x | case_eq x; intros]
          end in 
        match goal with 
          |- ?G => d G
        end. 
      d; simpl. 
      
      - compute in H.   
        inversion H0; subst; intuition; subst. 
        
        + constructor; auto. 
        + exfalso; clear - H1 H2. destruct x1.  simpl in *. 
          compute in H1; destruct val;
          omega || discriminate.
        
      - compute in H. inversion H0; subst; intuition; subst.   
        + compute in H1. discriminate. 
        + simpl; intuition. 
    Qed. 
    (*
    Inductive star {A} R : A -> A -> Prop :=
    | star_refl: forall a,
                   star R a a
    | star_step: forall a b c,
                   R a b -> star R b c -> star R a c.
    
    Notation "s ~~>* s'" := (star trans s s') (no associativity, at level 80). 
    Lemma sub_idem n (x : Word.T n)  : Word.sub x x = Word.repr n 0. 
    Proof. Admitted. 
    
    Lemma add_zero n (x : Word.T n)  : Word.add x (Word.repr n 0) = x. 
    Proof. Admitted. 
    
    Lemma mul_zero n (x : Word.T n) : Word.mul x (Word.repr n 0) = Word.repr n 0. 
    Proof. 
    Admitted. 
    
    Lemma trans_is_mult  s1 s2:
      s1 ~~> s2 ->
      forall n m acc, s1 = (n,m,acc) ->      
      match s2 with (n',m',acc') => 
                     n = n' /\ acc' = Word.add acc (Word.mul n (Word.sub m m')) 
      end. 
    Proof. 
      intros H. inversion H; intros; subst. 
      injection H2; intros; subst; intuition.
      rewrite sub_idem. rewrite mul_zero. rewrite add_zero. reflexivity. 
      injection H3; intros; subst. split; auto. 
      rewrite
      subst.       induction H; intuition; subst. 
      rewrite sub_idem. rewrite mul_zero. rewrite add_zero. auto. 

      destruct c as [[n'' m''] acc'']. 
      destruct b as [[n' m'] acc']. 
      specialize (IHstar n' m' acc' eq_refl). destruct IHstar. split; auto. 
      
      *)
  End correct. 
End t. 

Require Compiler. 
Require Import FirstOrder Core.
Eval vm_compute in Compiler.fesiopt (Phi 5) _ (mult 5). 
Eval vm_compute in Compiler.fesic (Phi 5) _ (mult 5). 
    
    