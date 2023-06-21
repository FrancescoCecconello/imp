(* FRANCESCO CECCONELLO VR457796 20/06/2023 *)

Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
From Coq Require Import Unicode.Utf8.

(* Definizione degli identificatori *)
Inductive id : Type :=
  | Id : nat -> id.

(* Definizione della mappa *)
Definition mappa (A:Type) := id -> A.

(* Definizione dello stato vuoto *)
Definition t_empty {A:Type} (v : A) : mappa A :=
  (fun _ => v).

(* Definizione dell'uguaglianza tra identificatori (serve per la funzione di aggiornamento) *)
Definition beq_id id1 id2 :=
  match id1, id2 with
  | Id n1, Id n2 => Nat.eqb n1 n2
  end.

(* Definizione dell'aggiornamento di una mappa totale *)
Definition aggiorna_stato {A:Type} (m : mappa A)
                    (x : id) (v : A) :=
  fun x' => if beq_id x x' then v else m x'.

(* Definizione degli stati *)
Definition stato := mappa nat.

(* Stato vuoto *)
Definition stato_vuoto : stato :=
  t_empty 0.

(* Definizione delle espressioni aritmetiche *)
Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : id -> aexp
  | APiu : aexp -> aexp -> aexp
  | AMeno : aexp -> aexp -> aexp
  | AMolt : aexp -> aexp -> aexp.

(* Definizione delle espressioni booleane *)
Inductive bexp : Type :=
  | BVero : bexp
  | BFalso : bexp
  | BNot : bexp -> bexp
  | BUguale : aexp -> aexp -> bexp
  | BMinoreUguale : aexp -> aexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

(* Definizione dei comandi *)
Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

(* Funzione di valutazione per le espressioni aritmetiche *)
Fixpoint aeval (a : aexp) (st : stato) : nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | APiu a1 a2 => (aeval a1 st) + (aeval a2 st)
  | AMeno a1 a2 => (aeval a1 st) - (aeval a2 st)
  | AMolt a1 a2 => (aeval a1 st) * (aeval a2 st)
  end.

(* Funzione di valutazione per le espressioni booleane *)
Fixpoint beval (b : bexp) (st : stato) : bool :=
  match b with
  | BVero => true
  | BFalso => false
  | BNot b' => negb (beval b' st)
  | BUguale a1 a2 => (aeval a1 st) =? (aeval a2 st)
  | BMinoreUguale a1 a2 => (aeval a1 st) <=? (aeval a2 st)
  | BAnd b1 b2 => andb (beval b1 st) (beval b2 st)
  end.

Notation "a1 'mu' a2" := 
  (BMinoreUguale a1 a2) (at level 60, right associativity).
Notation "'Skip'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'While' b 'do' c " :=
  (CWhile b c) (at level 80, right associativity).
Notation "'If' c1 'then' c2 'else' c3" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

(* Regole di valutazione per i comandi *)
Reserved Notation "'esegui' c1 'in' st 'ritorna' st'" (at level 40, st at level 39).

Inductive ceval : com -> stato -> stato -> Prop :=
| E_Skip : forall st,
    esegui CSkip in st ritorna st
| E_Ass : forall st a1 n x,
    aeval a1 st = n ->
    esegui (x ::= a1) in st ritorna (aggiorna_stato st x n)
| E_Seq : forall c1 c2 st st' st'',
    esegui c1 in st ritorna st' ->
    esegui c2 in st' ritorna st'' ->
    esegui (c1 ;; c2) in st ritorna st''
| E_IfTrue : forall st st' b c1 c2,
    beval b st = true ->
    esegui c1 in st ritorna st' ->
    esegui (CIf b c1 c2) in st ritorna st'
| E_IfFalse : forall st st' b c1 c2,
    beval b st = false ->
    esegui c2 in st ritorna st' ->
    esegui (CIf b c1 c2) in st ritorna st'
| E_WhileFalse : forall b st c,
    beval b st = false ->
    esegui (CWhile b c) in st ritorna st
| E_WhileTrue : forall st st' st'' b c,
    beval b st = true ->
    esegui c in st ritorna st' ->
    esegui (CWhile b c) in st' ritorna st'' ->
    esegui (CWhile b c) in st ritorna st''

where "'esegui' c1 'in' st 'ritorna' st'" := (ceval c1 st st').

(* Definizione relazione di equivalenza fra comandi come da slide *)
Definition cequiv (c1 c2 : com) : Prop :=
  ∀(st st' : stato),
    (esegui c1 in st ritorna st') ↔ (esegui c2 in st ritorna st').

Theorem equivalenza_if_while: ∀ (b: bexp) (c: com),
  cequiv
    (While b do c)
    (If b then (c;; While b do c) else Skip).
Proof.
  intros b c st st'.
  split; intros Hce.
  - (* -> *)
    inversion Hce; subst.
    + (* non entro nel ciclo*)
      apply E_IfFalse. assumption. apply E_Skip.
    + (* entro nel ciclo *)
      apply E_IfTrue. assumption.
      apply E_Seq with (st' := st'0). assumption. assumption.
  - (* <- *)
    inversion Hce; subst.
    + (* entro nel ciclo *)
      inversion H5. subst.
      apply E_WhileTrue with (st' := st'0).
      assumption. assumption. assumption.
    + (* non entro nel ciclo *)
      inversion H5; subst. apply E_WhileFalse. assumption.
Qed.

(* Definisco le variabili X e Y dell'algoritmo *)
Definition X : id := Id 0.
Definition Y : id := Id 1.

Example algoritmo:
  esegui
  (X ::= ANum 2;; (* x = 2 *)
   Y ::= ANum 3;; (* y = 3 *)
   While BMinoreUguale (ANum 1) (AId X) do (* controllo della condizione *)
     X ::= AMeno (AId X) (ANum 1);; (* x = x -1 *)
     Y ::= AMolt (ANum 2) (AId Y)   (* y = y * 2 *)
   )
  in stato_vuoto
  ritorna (aggiorna_stato (aggiorna_stato (aggiorna_stato (aggiorna_stato (aggiorna_stato (aggiorna_stato stato_vuoto X 2) Y 3) X 1) Y 6) X 0) Y 12). (* sequenza di cambiamento degli stati *)
Proof.
  apply E_Seq with (aggiorna_stato stato_vuoto X 2). (* aggiungo X = 2 allo stato vuoto *)
  - apply E_Ass. reflexivity. (* applico l'assegnamento *)
  - apply E_Seq with (aggiorna_stato (aggiorna_stato stato_vuoto X 2) Y 3). (* aggiungo X = 2, Y = 3 allo stato vuoto *)
    + apply E_Ass. reflexivity. (* applico l'assegnamento *)
    + apply E_WhileTrue with 
            (aggiorna_stato (aggiorna_stato (aggiorna_stato (aggiorna_stato stato_vuoto X 2) Y 3) X 1) Y 6). (* la condizione è vera *)
      * reflexivity. (* entro nel ciclo riportando lo stato finale dopo la prima iterazione con X = 1 e Y = 6*)
      * apply E_Seq with (aggiorna_stato (aggiorna_stato (aggiorna_stato stato_vuoto X 2) Y 3) X 1). (* aggiorno lo stato *)
        ** apply E_Ass. reflexivity. (* assegno X *)
        ** apply E_Ass. reflexivity. (* assegno Y *)
      * apply E_WhileTrue with 
            (aggiorna_stato (aggiorna_stato (aggiorna_stato (aggiorna_stato (aggiorna_stato (aggiorna_stato stato_vuoto X 2) Y 3) X 1) Y 6) X 0) Y 12).
            (* la condizione è ancora vera, quindi devo rientrare nel ciclo con lo stato precedente e riportando lo stato finale dopo la seconda iterazione *)
            (* con X = 0 e Y = 12 *)
        ** reflexivity. (* entro nel ciclo *)
        ** apply E_Seq with (aggiorna_stato (aggiorna_stato (aggiorna_stato (aggiorna_stato (aggiorna_stato stato_vuoto X 2) Y 3) X 1) Y 6) X 0). (* aggiorno lo stato *)
           *** apply E_Ass. reflexivity. (* assegno X *)
           *** apply E_Ass. reflexivity. (* assegno Y *)
        ** apply E_WhileFalse. reflexivity. (* la condizione è falsa, quindi esco dal ciclo *)
Qed.
