import Game.Metadata
-- https://philosophy.hku.hk/think/logic/knights.php
--Puzzle #201 out of 382
--
--A very special island is inhabited only by knights and knaves. Knights always tell the truth, and knaves always lie.
--
--You meet six inhabitants: Joe, Bob, Ted, Zippy, Alice and Zoey. Joe claims, “At least one of the following is true: that I am a knight or that Alice is a knave.” Bob says, “I could say that Zippy is a knight.” Ted tells you that Zippy is a knight and Alice is a knave. Zippy says that it's false that Bob is a knave. Alice tells you, “Either Zippy is a knave or Zoey is a knight.” Zoey tells you that it's not the case that Joe is a knave.
--
--Can you determine who is a knight and who is a knave?

--def Joe: Prop :=sorry
--def Bob : Prop:=sorry
--def Ted: Prop :=sorry
--def Zippy : Prop:=sorry
--def Alice: Prop :=sorry
--def Zoey : Prop:=sorry
variable ( Joe Bob Ted Zippy Alice Zoey : Prop)
--def knight(x:Prop):=x
--def knave(x:Prop):=¬x
--axiom Joe_stat:Joe  ↔  Joe ∨ ¬ Alice
--axiom Bob_stat: Bob  ↔  Zippy
--axiom Ted_stat: Ted  ↔ ( Zippy ∧ ¬ Alice)
--axiom Zippy_stat: Zippy  ↔  Bob
--axiom Alice_stat: Alice  ↔  (¬ Zippy ∨ Zoey)
--axiom Zoey_stat: Zoey  ↔ Joe

/-
prolog 
sat( (Joe =:= (Joe + ~Alice)) * (Bob =:= (Zippy)) * (Ted =:= (Zippy * ~Alice) * (Zippy =:= Bob)) * (Alice =:= (~Zippy + Zoey)) * (Zoey =:= Joe) ), labeling([Joe,Alice,Bob,Zippy,Zoey,Ted]).

Joe = Bob, Bob = Zippy, Zippy = Ted, Ted = Zoey, Zoey = 0,
Alice = 1 .

-/



example
(Joe_stat:Joe  ↔  Joe ∨ ¬ Alice)
(Bob_stat: Bob  ↔  Zippy)
(Ted_stat: Ted  ↔ ( Zippy ∧ ¬ Alice))
(Zippy_stat: Zippy  ↔  Bob)
(Alice_stat: Alice  ↔  (¬ Zippy ∨ Zoey))
(Zoey_stat: Zoey  ↔ Joe)
:(Alice ∧ ¬Ted)
:= by

  rw [Zoey_stat] at Alice_stat

  rcases em Joe with JoeKnight|JoeKnave
  · rcases em Ted with TedKnight|TedKnave
    · rcases em Alice with AliceKnight|AliceKnave
      · have ⟨a,b⟩ := Ted_stat.mp TedKnight
        contradiction 
      · have := Function.mt (Alice_stat.mpr) AliceKnave
        push_neg at this
        have := this.right
        contradiction
    · rcases em Alice with AliceKnight|AliceKnave
      · 
        constructor
        · assumption
        · assumption

      · 
        have := Function.mt Alice_stat.mpr AliceKnave
        rw [not_or] at this
        have := this.right
        contradiction


  · rcases em Ted with TedKnight|TedKnave
    · rcases em Alice with AliceKnight|AliceKnave
      · have := Ted_stat.mp TedKnight
        have := this.right
        contradiction

      · have := Function.mt Joe_stat.mpr JoeKnave
        push_neg at this
        have := this.right
        contradiction
    · rcases em Alice with AliceKnight|AliceKnave
      · 
        constructor
        assumption
        assumption
      · have := Function.mt Joe_stat.mpr JoeKnave
        push_neg at this
        have := this.right
        contradiction
     
