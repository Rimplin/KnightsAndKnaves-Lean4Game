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
     

--You have met a group of 3 islanders. Their names are Oberon, Tracy, and Wendy.
--
--    Tracy says: Wendy is untruthful.
--    Oberon says: Tracy is a knight and I am a knave.
--    Wendy says: Oberon is a knave.  Solution :     Because Oberon said 'Tracy is a knight and I am a knave,' we know Oberon is not making a true statement. (If it was true, the speaker would be a knight claiming to be a knave, which cannot happen.) Therefore, Oberon is a knave and Tracy is a knave.
--    All islanders will call a member of the opposite type a knave. So when Tracy says that Wendy is a knave, we know that Wendy and Tracy are opposite types. Since Tracy is a knave, then Wendy is a knight.
--
--For these reasons we know the knaves were Tracy and Oberon, and the only knight was Wendy.
--inductive person: Type | Tracy |Oberon| Wendy open person
--inductive type: Type|knight|knave open type
--variable (t:person → type)
--def stat(p:person): Prop := match p with
--|Tracy => t Wendy = knave 
--| Oberon => t Tracy = knight ∧ t Oberon = knave 
--| Wendy => t Oberon = knave 
--def solution:Prop:= t Tracy =knave ∧ t Oberon=knave ∧ t Wendy =knight 
--example : solution t:= by
--  unfold solution
--  -- take all cases
--  if (t Tracy) 
--  -- cases, but doesn't appear that tracy is a kngiht, cant see that tracy is a knight
--    sorry
--  else 
--    sorry
--
--
--  /-
--  cases Tracy
--    · cases Oberon
--      · cases Wendy
--        · sorry
--        · sorry
--        sorry
--     · cases Wendy
--       · sorry
--        · sorry
--        sorry
--    · cases Oberon
--     · cases Wendy
--        · sorry
--       · sorry
--       sorry
--      · cases Wendy
--      · sorry
--      · sorry
--      sorry
--      -/
--  -- and show the goal ... 
----exists(λ p,match p with | Tracy =>knave|Oberon=>knave | Wendy => knight ),split { refl}, split, { refl }, { refl } 



--Here is your puzzle:
--
--You have met a group of 3 islanders. Their names are Xavier, Gary, and Alice.
--
--    Gary says: Alice is my type.
--    Alice says: Gary never lies.
--    Gary says: Xavier never lies.
--solution:    A knight or a knave will say they are the same type as a knight. So when Gary says they are the same type as Alice, we know that Alice is a knight.
--    All islanders will call one of their same kind a knight. So when Alice says that Gary is a knight, we know that Gary and Alice are the same type. Since Alice is a knight, then Gary is a knight.
--    All islanders will call one of their same kind a knight. So when Gary says that Xavier is a knight, we know that Xavier and Gary are the same type. Since Gary is a knight, then Xavier is a knight.
--
--For these reasons we know there were no knaves , and the knights were Alice, Xavier, and Gary.
------------------
--Here is your puzzle:
--
--You have met a group of 2 islanders. Their names are Robert and Ira.
--
--    Robert says: Ira is my type.
--    Ira says: Robert is truthful.
--solution:     A knight or a knave will say they are the same type as a knight. So when Robert says they are the same type as Ira, we know that Ira is a knight.
--    All islanders will call one of their same kind a knight. So when Ira says that Robert is a knight, we know that Robert and Ira are the same type. Since Ira is a knight, then Robert is a knight.
--
--For these reasons we know there were no knaves , and the knights were Robert and Ira.
