variable (p2 p1 p6 p0 p4 p7 p5 p3 : Prop)
theorem file25_50 : (((((p4 ∨ p3) ∨ (False ∧ p7)) → ((p0 → p2) ∧ (p3 → p6))) ∨ (((p6 ∨ p3) ∨ (p3 → False)) ∨ ((p1 ∨ p1) → (p2 ∨ p7)))) → ((((p6 → p3) → (False → False)) ∧ ((True ∨ p4) ∨ (p4 → p2))) ∨ (((p5 ∨ p7) → (p1 → False)) → ((p4 → False) ∧ (p7 → False))))) := by
  intro assump_14
  cases assump_14
  case inl assump_15 =>
    apply Or.inl
    apply And.intro
    intro assump_19
    intro assump_20
    apply False.elim assump_20
    apply Or.inl
    apply Or.inl
    apply True.intro
  case inr assump_16 =>
    cases assump_16
    case inl assump_23 =>
      cases assump_23
      case inl assump_25 =>
        cases assump_25
        case inl assump_27 =>
          apply Or.inl
          apply And.intro
          intro assump_31
          intro assump_32
          apply False.elim assump_32
          apply Or.inl
          apply Or.inl
          apply True.intro
        case inr assump_28 =>
          apply Or.inl
          apply And.intro
          intro assump_37
          intro assump_38
          apply False.elim assump_38
          apply Or.inl
          apply Or.inl
          apply True.intro
      case inr assump_26 =>
        apply Or.inl
        apply And.intro
        intro assump_43
        intro assump_44
        apply False.elim assump_44
        apply Or.inl
        apply Or.inl
        apply True.intro
    case inr assump_24 =>
      apply Or.inl
      apply And.intro
      intro assump_49
      intro assump_50
      apply False.elim assump_50
      apply Or.inl
      apply Or.inl
      apply True.intro


variable (p7 p1 p6 p5 : Prop)
theorem file25_1630 : (((((p6 ∧ p5) ∧ (p1 ∧ False)) → ((p5 ∧ p7) → False)) → False) → False) := by
  intro assump_1
  have assump_30 : (((p6 ∧ p5) ∧ (p1 ∧ False)) → ((p5 ∧ p7) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_5
      case intro assump_13 assump_14 =>
        cases assump_13
        case intro assump_15 assump_16 =>
          cases assump_14
          case intro assump_21 assump_22 =>
            apply False.elim assump_22
  let assump_4 := assump_1 assump_30
  apply False.elim assump_4


variable (p0 p1 p3 p2 p4 : Prop)
theorem file25_2251 : ((((((False ∧ p4) ∧ (True ∧ p3)) → False) ∨ (((True → False) → (p2 → False)) ∧ ((p0 ∧ p1) → (p3 → p0)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((False ∧ p4) ∧ (True ∧ p3)) → False) ∨ (((True → False) → (p2 → False)) ∧ ((p0 ∧ p1) → (p3 → p0)))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p3 p6 p5 p7 p1 p2 p0 : Prop)
theorem file25_2837 : ((((((p1 → p0) → (p2 → False)) ∧ ((p2 ∨ False) ∨ (False ∨ p3))) ∧ (((False ∨ p1) ∧ (p7 ∧ False)) ∧ ((p7 ∨ p1) → False))) ∨ ((((True ∧ p1) → False) ∧ ((p1 → False) ∧ (p1 ∧ False))) ∧ (((p6 ∨ p1) → (p5 ∧ p5)) ∧ ((p5 → False) ∧ (p6 ∨ p7))))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case inl assump_10 =>
          cases assump_10
          case inl assump_12 =>
            cases assump_5
            case intro assump_16 assump_17 =>
              cases assump_16
              case intro assump_18 assump_19 =>
                cases assump_18
                case inl assump_20 =>
                  apply False.elim assump_20
                case inr assump_21 =>
                  cases assump_19
                  case intro assump_26 assump_27 =>
                    apply False.elim assump_27
          case inr assump_13 =>
            apply False.elim assump_13
        case inr assump_11 =>
          cases assump_11
          case inl assump_34 =>
            apply False.elim assump_34
          case inr assump_35 =>
            cases assump_5
            case intro assump_40 assump_41 =>
              cases assump_40
              case intro assump_42 assump_43 =>
                cases assump_42
                case inl assump_44 =>
                  apply False.elim assump_44
                case inr assump_45 =>
                  cases assump_43
                  case intro assump_50 assump_51 =>
                    apply False.elim assump_51
  case inr assump_3 =>
    cases assump_3
    case intro assump_56 assump_57 =>
      cases assump_56
      case intro assump_58 assump_59 =>
        cases assump_59
        case intro assump_62 assump_63 =>
          cases assump_63
          case intro assump_66 assump_67 =>
            apply False.elim assump_67


variable (p4 p3 p6 p5 p7 p0 : Prop)
theorem file25_4854 : (((((p5 ∨ False) → False) → ((True ∧ p3) → False)) ∧ (((True → False) → (p7 → False)) → False)) → ((((True → p0) → False) ∨ ((p0 ∨ p4) ∧ (p6 ∧ p0))) ∨ (((True → p6) → False) ∨ ((p6 → False) → False)))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    apply Or.inl
    intro assump_8
    have assump_27 : ((True → False) → (p7 → False)) := by
      intro assump_14
      intro assump_15
      have assump_28 : True := by
        apply True.intro
      let assump_20 := assump_14 assump_28
      apply False.elim assump_20
    let assump_13 := assump_3 assump_27
    apply False.elim assump_13


variable (p2 p3 p6 p0 p1 p4 p5 : Prop)
theorem file25_5555 : (((((False ∧ True) → False) → False) → (((p4 ∨ p0) ∨ (p5 → False)) ∧ ((p3 ∨ p6) ∨ (p1 ∨ False)))) ∨ ((((p2 ∧ p1) → False) ∧ ((p6 → False) → False)) ∧ (((False ∧ p4) ∨ (p2 → p0)) ∧ ((p1 ∨ p6) → (p4 → p0))))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  apply Or.inr
  intro assump_4
  have assump_28 : ((False ∧ True) → False) := by
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      apply False.elim assump_10
  let assump_8 := assump_1 assump_28
  apply False.elim assump_8
  have assump_29 : ((False ∧ True) → False) := by
    intro assump_20
    cases assump_20
    case intro assump_21 assump_22 =>
      apply False.elim assump_21
  let assump_19 := assump_1 assump_29
  apply False.elim assump_19


variable (p3 p1 p0 p2 p5 p4 : Prop)
theorem file25_6362 : (((((False → False) → False) ∧ ((True ∨ p1) ∧ (p4 ∧ p3))) → False) ∨ ((((p5 ∨ True) → (p1 ∧ p0)) ∧ ((p4 ∨ p0) → (p1 → False))) ∧ (((p2 ∧ p0) → False) ∧ ((p3 → p2) → False)))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case intro assump_12 assump_13 =>
          have assump_45 : (False → False) := by
            intro assump_21
            apply False.elim assump_21
          let assump_20 := assump_2 assump_45
          apply False.elim assump_20
      case inr assump_9 =>
        cases assump_7
        case intro assump_29 assump_30 =>
          have assump_46 : (False → False) := by
            intro assump_39
            apply False.elim assump_39
          let assump_38 := assump_2 assump_46
          apply False.elim assump_38


variable (p6 p7 p5 p4 p0 p3 p1 p2 : Prop)
theorem file25_7350 : (((((p1 → False) → False) → ((p1 ∧ p4) → False)) ∧ (((p6 → False) → False) → ((p4 ∧ p0) ∨ (p7 ∧ p4)))) → ((((False ∨ p7) → (p3 ∧ p2)) ∧ ((False ∧ p2) ∧ (p4 ∨ False))) → (((False → False) ∨ (p7 → p5)) ∧ ((p4 ∧ p2) ∧ (True ∧ p7))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        apply False.elim assump_9
  apply And.intro
  apply And.intro
  cases assump_2
  case intro assump_13 assump_14 =>
    cases assump_14
    case intro assump_17 assump_18 =>
      cases assump_17
      case intro assump_19 assump_20 =>
        apply False.elim assump_19
  cases assump_2
  case intro assump_23 assump_24 =>
    cases assump_24
    case intro assump_27 assump_28 =>
      cases assump_27
      case intro assump_29 assump_30 =>
        apply False.elim assump_29
  apply And.intro
  apply True.intro
  cases assump_2
  case intro assump_33 assump_34 =>
    cases assump_34
    case intro assump_37 assump_38 =>
      cases assump_37
      case intro assump_39 assump_40 =>
        apply False.elim assump_39


variable (p3 p0 p6 p5 p7 p2 : Prop)
theorem file25_8596 : ((((((p0 ∨ p7) ∨ (p6 ∧ p6)) ∧ ((p3 → False) → (p2 ∧ p0))) → False) ∧ ((((True → False) ∧ (p5 ∧ p3)) → ((p7 → False) → (p3 ∨ False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_26 : (((True → False) ∧ (p5 ∧ p3)) → ((p7 → False) → (p3 ∨ False))) := by
      intro assump_9
      intro assump_10
      cases assump_9
      case intro assump_13 assump_14 =>
        cases assump_14
        case intro assump_17 assump_18 =>
          apply Or.inl
          exact assump_18
    let assump_8 := assump_3 assump_26
    apply False.elim assump_8


variable (p4 p3 : Prop)
theorem file25_9248 : (((((p4 ∨ True) → False) → ((p3 → False) → False)) → False) → False) := by
  intro assump_5
  have assump_22 : (((p4 ∨ True) → False) → ((p3 → False) → False)) := by
    intro assump_9
    intro assump_10
    have assump_23 : (p4 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_15 := assump_9 assump_23
    apply False.elim assump_15
  let assump_8 := assump_5 assump_22
  apply False.elim assump_8


variable (p3 p7 p4 p6 p0 p2 p5 p1 : Prop)
theorem file25_9736 : (((((p2 → p1) ∨ (p1 → False)) → ((False → False) ∧ (p2 ∧ p3))) → (((True ∨ p0) ∨ (p6 → False)) ∧ ((p5 ∨ p2) ∧ (False → False)))) → ((((p7 ∨ p6) ∨ (p7 ∧ p5)) → ((p1 → p2) → (p4 ∧ p5))) → (((p3 ∧ p7) ∧ (p4 → False)) → ((p0 ∧ p3) ∨ (False ∨ p3))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_4
    case intro assump_6 assump_7 =>
      apply Or.inr
      apply Or.inr
      exact assump_6


variable (p0 p4 p3 p6 p5 p2 p7 p1 : Prop)
theorem file25_10270 : (((((p5 ∨ p5) ∧ (p1 → p4)) → ((False → False) → (p0 → False))) ∨ (((p4 → p0) → False) ∨ ((p1 ∧ False) ∧ (False → False)))) → ((((True → False) → False) → ((False → True) ∧ (p6 → True))) ∧ (((True → False) → (p0 → p3)) ∨ ((False → p7) → (p1 ∨ p2))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  apply And.intro
  intro assump_3
  apply True.intro
  intro assump_4
  apply True.intro
  cases assump_1
  case inl assump_5 =>
    apply Or.inl
    intro assump_9
    intro assump_10
    have assump_41 : True := by
      apply True.intro
    let assump_15 := assump_9 assump_41
    apply False.elim assump_15
  case inr assump_6 =>
    cases assump_6
    case inl assump_19 =>
      apply Or.inl
      intro assump_23
      intro assump_24
      have assump_42 : True := by
        apply True.intro
      let assump_29 := assump_23 assump_42
      apply False.elim assump_29
    case inr assump_20 =>
      cases assump_20
      case intro assump_33 assump_34 =>
        cases assump_33
        case intro assump_35 assump_36 =>
          apply False.elim assump_36


variable (p3 p1 p6 p5 p4 : Prop)
theorem file25_11404 : ((((((False ∧ p3) ∧ (p6 ∨ p5)) → ((True → p5) → False)) ∨ (((p1 ∨ True) ∧ (p3 → False)) ∨ ((p4 ∧ p6) → False))) → False) → False) := by
  intro assump_37
  have assump_54 : ((((False ∧ p3) ∧ (p6 ∨ p5)) → ((True → p5) → False)) ∨ (((p1 ∨ True) ∧ (p3 → False)) ∨ ((p4 ∧ p6) → False))) := by
    apply Or.inl
    intro assump_41
    intro assump_42
    cases assump_41
    case intro assump_45 assump_46 =>
      cases assump_45
      case intro assump_47 assump_48 =>
        apply False.elim assump_47
  let assump_40 := assump_37 assump_54
  apply False.elim assump_40


variable (p3 p4 p2 p1 p5 p6 p0 : Prop)
theorem file25_12036 : (((((p3 → p4) → (False → p4)) → ((p5 → False) ∧ (p5 ∧ p2))) → False) → ((((False → False) ∧ (True ∨ p5)) ∨ ((p2 ∧ p0) ∨ (False ∧ p5))) ∨ (((p6 ∨ p1) → (p3 ∧ p6)) ∨ ((p2 ∧ p0) ∨ (p0 ∧ p3))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply And.intro
  intro assump_4
  apply False.elim assump_4
  apply Or.inl
  apply True.intro


variable (p4 p2 p0 p7 p6 p1 p3 : Prop)
theorem file25_12440 : ((((((p2 → True) → (p2 → p1)) ∨ ((p2 → p2) → False)) → False) ∧ ((((p0 ∧ p6) ∧ (p6 ∨ p7)) ∨ ((True ∨ True) ∨ (p3 → p4))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_12 : (((p0 ∧ p6) ∧ (p6 ∨ p7)) ∨ ((True ∨ True) ∨ (p3 → p4))) := by
      apply Or.inr
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_8 := assump_3 assump_12
    apply False.elim assump_8


variable (p1 p0 p6 p4 p3 p2 p7 : Prop)
theorem file25_12949 : (((((False → p6) → False) ∨ ((p3 → p7) ∨ (p4 ∧ p2))) → (((False ∧ p0) → (False → False)) ∨ ((p1 → False) ∨ (True ∧ p1)))) ∨ ((((p1 → p7) → (p6 ∨ p3)) ∧ ((p2 → False) ∧ (p6 → False))) ∧ (((p7 → p4) → (p3 → False)) ∧ ((p3 → p6) ∨ (p1 → p3))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    intro assump_7
    apply False.elim assump_7
  case inr assump_3 =>
    cases assump_3
    case inl assump_10 =>
      apply Or.inl
      intro assump_14
      intro assump_15
      apply False.elim assump_15
    case inr assump_11 =>
      cases assump_11
      case intro assump_18 assump_19 =>
        apply Or.inl
        intro assump_24
        intro assump_25
        apply False.elim assump_25


variable (p7 p3 p6 p1 p5 p2 p4 : Prop)
theorem file25_13773 : ((((((p4 → False) → False) ∧ ((p5 ∨ p3) ∧ (False ∨ False))) ∧ (((p5 ∧ p4) ∨ (p4 → False)) → False)) ∧ ((((p5 → False) ∧ (p1 ∨ p1)) → False) → (((p5 → False) ∧ (p7 → False)) ∨ ((p5 → p2) → (p6 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          cases assump_10
          case inl assump_12 =>
            cases assump_11
            case inl assump_16 =>
              apply False.elim assump_16
            case inr assump_17 =>
              apply False.elim assump_17
          case inr assump_13 =>
            cases assump_11
            case inl assump_24 =>
              apply False.elim assump_24
            case inr assump_25 =>
              apply False.elim assump_25


variable (p1 p3 p4 : Prop)
theorem file25_14737 : ((((((p4 ∧ False) ∧ (False → p1)) ∧ ((False → p4) → (p3 ∧ True))) → False) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p4 ∧ False) ∧ (False → p1)) ∧ ((False → p4) → (p3 ∧ True))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply False.elim assump_11
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p1 p7 p2 p3 p6 p4 : Prop)
theorem file25_15311 : ((((((p3 → p4) ∨ (p6 → False)) → False) ∧ (((p3 → p3) → (p4 ∧ p4)) ∧ ((p7 ∨ p1) → False))) ∧ ((((False ∧ p6) ∧ (True → False)) → ((False → False) → False)) ∨ (((p4 ∧ p4) → (p4 → False)) ∧ ((p6 → False) ∧ (p3 → p2))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_3
        case inl assump_14 =>
          have assump_83 : ((p3 → p4) ∨ (p6 → False)) := by
            apply Or.inl
            intro assump_28
            have assump_84 : (p3 → p3) := by
              intro assump_35
              exact assump_35
            let assump_34 := assump_8 assump_84
            let assump_38 := And.left assump_34
            exact assump_38
          let assump_27 := assump_4 assump_83
          apply False.elim assump_27
        case inr assump_15 =>
          cases assump_15
          case intro assump_43 assump_44 =>
            cases assump_44
            case intro assump_47 assump_48 =>
              have assump_85 : ((p3 → p4) ∨ (p6 → False)) := by
                apply Or.inl
                intro assump_65
                have assump_86 : (p3 → p3) := by
                  intro assump_75
                  exact assump_75
                let assump_74 := assump_8 assump_86
                let assump_78 := And.left assump_74
                exact assump_78
              let assump_64 := assump_4 assump_85
              apply False.elim assump_64


variable (p7 p1 p4 p2 p5 p0 p6 : Prop)
theorem file25_16910 : ((((((p4 ∧ p2) ∧ (p1 → False)) ∧ ((p2 → False) → (p5 ∧ p6))) ∧ (((p5 → False) ∨ (p5 → False)) ∧ ((False ∨ True) ∧ (p0 ∧ p4)))) ∧ ((((False ∨ p5) ∧ (p7 → p0)) → ((True ∨ p2) ∧ (p4 ∧ p2))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_8
          case intro assump_10 assump_11 =>
            cases assump_5
            case intro assump_20 assump_21 =>
              cases assump_20
              case inl assump_22 =>
                cases assump_21
                case intro assump_26 assump_27 =>
                  cases assump_26
                  case inl assump_28 =>
                    apply False.elim assump_28
                  case inr assump_29 =>
                    cases assump_27
                    case intro assump_34 assump_35 =>
                      have assump_130 : (((False ∨ p5) ∧ (p7 → p0)) → ((True ∨ p2) ∧ (p4 ∧ p2))) := by
                        intro assump_43
                        apply And.intro
                        cases assump_43
                        case intro assump_44 assump_45 =>
                          cases assump_44
                          case inl assump_46 =>
                            apply False.elim assump_46
                          case inr assump_47 =>
                            apply Or.inl
                            apply True.intro
                        apply And.intro
                        cases assump_43
                        case intro assump_54 assump_55 =>
                          cases assump_54
                          case inl assump_56 =>
                            apply False.elim assump_56
                          case inr assump_57 =>
                            exact assump_35
                        cases assump_43
                        case intro assump_64 assump_65 =>
                          cases assump_64
                          case inl assump_66 =>
                            apply False.elim assump_66
                          case inr assump_67 =>
                            exact assump_11
                      let assump_42 := assump_3 assump_130
                      apply False.elim assump_42
              case inr assump_23 =>
                cases assump_21
                case intro assump_79 assump_80 =>
                  cases assump_79
                  case inl assump_81 =>
                    apply False.elim assump_81
                  case inr assump_82 =>
                    cases assump_80
                    case intro assump_87 assump_88 =>
                      have assump_131 : (((False ∨ p5) ∧ (p7 → p0)) → ((True ∨ p2) ∧ (p4 ∧ p2))) := by
                        intro assump_96
                        apply And.intro
                        cases assump_96
                        case intro assump_97 assump_98 =>
                          cases assump_97
                          case inl assump_99 =>
                            apply False.elim assump_99
                          case inr assump_100 =>
                            apply Or.inl
                            apply True.intro
                        apply And.intro
                        cases assump_96
                        case intro assump_107 assump_108 =>
                          cases assump_107
                          case inl assump_109 =>
                            apply False.elim assump_109
                          case inr assump_110 =>
                            exact assump_88
                        cases assump_96
                        case intro assump_117 assump_118 =>
                          cases assump_117
                          case inl assump_119 =>
                            apply False.elim assump_119
                          case inr assump_120 =>
                            exact assump_11
                      let assump_95 := assump_3 assump_131
                      apply False.elim assump_95


variable (p3 p4 p0 p6 p2 : Prop)
theorem file25_21103 : ((((((p4 ∧ p0) ∧ (p3 → False)) ∧ ((p0 → False) → False)) → False) ∧ ((((True → False) → False) → ((False → p3) → False)) ∧ (((p2 → True) ∨ (p0 → False)) ∧ ((p6 ∧ p3) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          have assump_56 : ((True → False) → False) := by
            intro assump_21
            have assump_57 : True := by
              apply True.intro
            let assump_24 := assump_21 assump_57
            apply False.elim assump_24
          let assump_20 := assump_6 assump_56
          have assump_58 : (False → p3) := by
            intro assump_29
            apply False.elim assump_29
          let assump_28 := assump_20 assump_58
          apply False.elim assump_28
        case inr assump_13 =>
          have assump_59 : ((True → False) → False) := by
            intro assump_42
            have assump_60 : True := by
              apply True.intro
            let assump_45 := assump_42 assump_60
            apply False.elim assump_45
          let assump_41 := assump_6 assump_59
          have assump_61 : (False → p3) := by
            intro assump_50
            apply False.elim assump_50
          let assump_49 := assump_41 assump_61
          apply False.elim assump_49


variable (p6 p2 p4 p0 p3 p7 p5 : Prop)
theorem file25_22603 : ((((((True → p2) ∨ (p2 → False)) → ((p3 → p7) → (p6 ∧ False))) → (((p7 → False) ∨ (p5 → p2)) → ((p4 ∨ False) → False))) ∧ ((((p5 ∨ False) ∨ (p7 ∨ p4)) ∨ ((p7 ∧ p0) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_25 : (((p5 ∨ False) ∨ (p7 ∨ p4)) ∨ ((p7 ∧ p0) → False)) := by
      apply Or.inr
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        have assump_26 : (((p5 ∨ False) ∨ (p7 ∨ p4)) ∨ ((p7 ∧ p0) → False)) := by
          apply Or.inl
          apply Or.inr
          apply Or.inl
          exact assump_10
        let assump_18 := assump_3 assump_26
        apply False.elim assump_18
    let assump_8 := assump_3 assump_25
    apply False.elim assump_8


variable (p7 p5 p6 p3 p2 p4 : Prop)
theorem file25_23434 : ((((((p2 → p5) → False) → ((p2 ∨ p2) → False)) ∨ (((p6 → False) → False) → False)) ∧ ((((p2 ∨ True) → (p5 ∧ p7)) ∧ ((False → p7) → False)) ∧ (((p3 ∨ p4) → (p4 → False)) ∧ ((p4 ∧ p2) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_9
          case intro assump_16 assump_17 =>
            have assump_56 : (False → p7) := by
              intro assump_25
              apply False.elim assump_25
            let assump_24 := assump_11 assump_56
            apply False.elim assump_24
    case inr assump_5 =>
      cases assump_3
      case intro assump_33 assump_34 =>
        cases assump_33
        case intro assump_35 assump_36 =>
          cases assump_34
          case intro assump_41 assump_42 =>
            have assump_57 : (False → p7) := by
              intro assump_50
              apply False.elim assump_50
            let assump_49 := assump_36 assump_57
            apply False.elim assump_49


variable (p7 p6 p0 p4 p5 : Prop)
theorem file25_24641 : ((((((p4 ∨ p7) → False) ∨ ((p5 → False) ∨ (p0 ∨ p7))) → (((p6 → p5) → False) → ((True ∨ p6) → (p5 → False)))) → False) → False) := by
  intro assump_13
  have assump_120 : ((((p4 ∨ p7) → False) ∨ ((p5 → False) ∨ (p0 ∨ p7))) → (((p6 → p5) → False) → ((True ∨ p6) → (p5 → False)))) := by
    intro assump_17
    intro assump_18
    intro assump_19
    intro assump_20
    cases assump_19
    case inl assump_23 =>
      cases assump_17
      case inl assump_29 =>
        have assump_121 : (p6 → p5) := by
          intro assump_35
          exact assump_20
        let assump_34 := assump_18 assump_121
        apply False.elim assump_34
      case inr assump_30 =>
        cases assump_30
        case inl assump_41 =>
          have assump_122 : p5 := by
            exact assump_20
          let assump_45 := assump_41 assump_122
          apply False.elim assump_45
        case inr assump_42 =>
          cases assump_42
          case inl assump_49 =>
            have assump_123 : (p6 → p5) := by
              intro assump_55
              exact assump_20
            let assump_54 := assump_18 assump_123
            apply False.elim assump_54
          case inr assump_50 =>
            have assump_124 : (p6 → p5) := by
              intro assump_65
              exact assump_20
            let assump_64 := assump_18 assump_124
            apply False.elim assump_64
    case inr assump_24 =>
      cases assump_17
      case inl assump_75 =>
        have assump_125 : (p6 → p5) := by
          intro assump_81
          exact assump_20
        let assump_80 := assump_18 assump_125
        apply False.elim assump_80
      case inr assump_76 =>
        cases assump_76
        case inl assump_87 =>
          have assump_126 : p5 := by
            exact assump_20
          let assump_91 := assump_87 assump_126
          apply False.elim assump_91
        case inr assump_88 =>
          cases assump_88
          case inl assump_95 =>
            have assump_127 : (p6 → p5) := by
              intro assump_101
              exact assump_20
            let assump_100 := assump_18 assump_127
            apply False.elim assump_100
          case inr assump_96 =>
            have assump_128 : (p6 → p5) := by
              intro assump_111
              exact assump_20
            let assump_110 := assump_18 assump_128
            apply False.elim assump_110
  let assump_16 := assump_13 assump_120
  apply False.elim assump_16


variable (p5 p6 p3 p1 p4 : Prop)
theorem file25_27145 : ((((((p4 ∨ p3) ∨ (True ∨ p4)) ∧ ((p1 ∧ p1) ∨ (p4 → False))) → (((p4 ∧ p1) → (p4 ∧ p1)) ∨ ((False → p6) → (p5 → p1)))) → ((((p1 ∨ True) → False) → ((p6 ∧ False) ∨ (False ∧ p4))) → False)) → False) := by
  intro assump_32
  have assump_208 : ((((p4 ∨ p3) ∨ (True ∨ p4)) ∧ ((p1 ∧ p1) ∨ (p4 → False))) → (((p4 ∧ p1) → (p4 ∧ p1)) ∨ ((False → p6) → (p5 → p1)))) := by
    intro assump_36
    cases assump_36
    case intro assump_37 assump_38 =>
      cases assump_37
      case inl assump_39 =>
        cases assump_39
        case inl assump_41 =>
          cases assump_38
          case inl assump_45 =>
            cases assump_45
            case intro assump_47 assump_48 =>
              apply Or.inl
              intro assump_53
              apply And.intro
              cases assump_53
              case intro assump_54 assump_55 =>
                exact assump_54
              cases assump_53
              case intro assump_60 assump_61 =>
                exact assump_61
          case inr assump_46 =>
            apply Or.inl
            intro assump_68
            apply And.intro
            cases assump_68
            case intro assump_69 assump_70 =>
              exact assump_69
            cases assump_68
            case intro assump_75 assump_76 =>
              exact assump_76
        case inr assump_42 =>
          cases assump_38
          case inl assump_83 =>
            cases assump_83
            case intro assump_85 assump_86 =>
              apply Or.inl
              intro assump_91
              apply And.intro
              cases assump_91
              case intro assump_92 assump_93 =>
                exact assump_92
              cases assump_91
              case intro assump_98 assump_99 =>
                exact assump_99
          case inr assump_84 =>
            apply Or.inl
            intro assump_106
            apply And.intro
            cases assump_106
            case intro assump_107 assump_108 =>
              exact assump_107
            cases assump_106
            case intro assump_113 assump_114 =>
              exact assump_114
      case inr assump_40 =>
        cases assump_40
        case inl assump_119 =>
          cases assump_38
          case inl assump_123 =>
            cases assump_123
            case intro assump_125 assump_126 =>
              apply Or.inl
              intro assump_131
              apply And.intro
              cases assump_131
              case intro assump_132 assump_133 =>
                exact assump_132
              cases assump_131
              case intro assump_138 assump_139 =>
                exact assump_139
          case inr assump_124 =>
            apply Or.inl
            intro assump_146
            apply And.intro
            cases assump_146
            case intro assump_147 assump_148 =>
              exact assump_147
            cases assump_146
            case intro assump_153 assump_154 =>
              exact assump_154
        case inr assump_120 =>
          cases assump_38
          case inl assump_161 =>
            cases assump_161
            case intro assump_163 assump_164 =>
              apply Or.inl
              intro assump_169
              apply And.intro
              cases assump_169
              case intro assump_170 assump_171 =>
                exact assump_170
              cases assump_169
              case intro assump_176 assump_177 =>
                exact assump_177
          case inr assump_162 =>
            apply Or.inl
            intro assump_184
            apply And.intro
            cases assump_184
            case intro assump_185 assump_186 =>
              exact assump_185
            cases assump_184
            case intro assump_191 assump_192 =>
              exact assump_192
  let assump_35 := assump_32 assump_208
  have assump_209 : (((p1 ∨ True) → False) → ((p6 ∧ False) ∨ (False ∧ p4))) := by
    intro assump_198
    have assump_210 : (p1 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_201 := assump_198 assump_210
    apply False.elim assump_201
  let assump_197 := assump_35 assump_209
  apply False.elim assump_197


variable (p6 p2 p1 p7 p0 p4 p5 p3 : Prop)
theorem file25_31366 : (((((p7 → False) ∧ (p2 → p6)) → False) → (((p7 ∧ p3) → (p5 ∧ p6)) → ((p2 ∨ True) ∨ (p1 ∨ p4)))) ∨ ((((p4 ∧ False) → (p0 → False)) ∧ ((p5 → True) → (p4 ∧ p6))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply Or.inl
  apply Or.inr
  apply True.intro


variable (p2 p5 p1 p4 p7 p0 p6 : Prop)
theorem file25_31702 : (((((p1 ∧ p1) ∨ (p7 ∧ p4)) ∨ ((p0 ∧ False) → False)) ∨ (((p6 ∧ p7) → False) ∨ ((p4 ∧ p6) ∨ (p5 → p4)))) ∧ ((((True ∧ False) → (p7 ∧ p2)) → False) → False)) := by
  apply And.intro
  apply Or.inl
  apply Or.inr
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply False.elim assump_3
  intro assump_8
  have assump_28 : ((True ∧ False) → (p7 ∧ p2)) := by
    intro assump_12
    apply And.intro
    cases assump_12
    case intro assump_13 assump_14 =>
      apply False.elim assump_14
    cases assump_12
    case intro assump_19 assump_20 =>
      apply False.elim assump_20
  let assump_11 := assump_8 assump_28
  apply False.elim assump_11


variable (p7 p0 p2 p6 p4 p3 p5 p1 : Prop)
theorem file25_32436 : (((((p4 ∨ p2) → False) ∨ ((p2 → p1) ∨ (False → p7))) ∨ (((p2 ∨ p3) ∧ (p1 ∧ p3)) ∧ ((p7 ∧ p4) → False))) → ((((True ∧ False) → False) → False) → (((p6 ∨ p5) ∨ (False ∧ p0)) ∨ ((p7 → p0) → (p4 → False))))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    cases assump_5
    case inl assump_7 =>
      apply Or.inr
      intro assump_11
      intro assump_12
      have assump_141 : (p4 ∨ p2) := by
        apply Or.inl
        exact assump_12
      let assump_19 := assump_7 assump_141
      apply False.elim assump_19
    case inr assump_8 =>
      cases assump_8
      case inl assump_23 =>
        apply Or.inr
        intro assump_27
        intro assump_28
        have assump_142 : ((True ∧ False) → False) := by
          intro assump_37
          cases assump_37
          case intro assump_38 assump_39 =>
            apply False.elim assump_39
        let assump_36 := assump_2 assump_142
        apply False.elim assump_36
      case inr assump_24 =>
        apply Or.inr
        intro assump_49
        intro assump_50
        have assump_143 : ((True ∧ False) → False) := by
          intro assump_59
          cases assump_59
          case intro assump_60 assump_61 =>
            apply False.elim assump_61
        let assump_58 := assump_2 assump_143
        apply False.elim assump_58
  case inr assump_6 =>
    cases assump_6
    case intro assump_69 assump_70 =>
      cases assump_69
      case intro assump_71 assump_72 =>
        cases assump_71
        case inl assump_73 =>
          cases assump_72
          case intro assump_77 assump_78 =>
            apply Or.inr
            intro assump_85
            intro assump_86
            have assump_144 : ((True ∧ False) → False) := by
              intro assump_98
              cases assump_98
              case intro assump_99 assump_100 =>
                apply False.elim assump_100
            let assump_97 := assump_2 assump_144
            apply False.elim assump_97
        case inr assump_74 =>
          cases assump_72
          case intro assump_110 assump_111 =>
            apply Or.inr
            intro assump_118
            intro assump_119
            have assump_145 : ((True ∧ False) → False) := by
              intro assump_131
              cases assump_131
              case intro assump_132 assump_133 =>
                apply False.elim assump_133
            let assump_130 := assump_2 assump_145
            apply False.elim assump_130


variable (p5 p1 p2 p7 p3 : Prop)
theorem file25_34970 : ((((((p2 ∧ p1) ∨ (p3 → True)) → False) → (((p5 → p3) → False) ∨ ((p5 → False) → (p7 → False)))) → False) → False) := by
  intro assump_1
  have assump_20 : ((((p2 ∧ p1) ∨ (p3 → True)) → False) → (((p5 → p3) → False) ∨ ((p5 → False) → (p7 → False)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    have assump_21 : ((p2 ∧ p1) ∨ (p3 → True)) := by
      apply Or.inr
      intro assump_13
      apply True.intro
    let assump_12 := assump_5 assump_21
    apply False.elim assump_12
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p0 p3 p6 p2 p7 p1 p4 p5 : Prop)
theorem file25_35600 : (((((False ∧ p4) ∨ (p7 → False)) ∧ ((p5 → p6) ∧ (p3 ∨ p4))) ∧ (((p3 → p2) ∨ (p3 ∨ p2)) ∧ ((p5 ∧ p2) ∨ (p6 ∨ False)))) → ((((p1 ∧ p1) ∧ (False → False)) → ((p3 ∧ p1) → (p6 ∧ p1))) ∧ (((p1 ∧ p1) → (p7 → p1)) ∧ ((p0 → p6) ∨ (p2 → False))))) := by
  intro assump_10
  apply And.intro
  intro assump_11
  intro assump_12
  apply And.intro
  cases assump_12
  case intro assump_13 assump_14 =>
    cases assump_11
    case intro assump_19 assump_20 =>
      cases assump_19
      case intro assump_21 assump_22 =>
        cases assump_10
        case intro assump_29 assump_30 =>
          cases assump_29
          case intro assump_31 assump_32 =>
            cases assump_31
            case inl assump_33 =>
              cases assump_33
              case intro assump_35 assump_36 =>
                apply False.elim assump_35
            case inr assump_34 =>
              cases assump_32
              case intro assump_41 assump_42 =>
                cases assump_42
                case inl assump_45 =>
                  cases assump_30
                  case intro assump_49 assump_50 =>
                    cases assump_49
                    case inl assump_51 =>
                      cases assump_50
                      case inl assump_55 =>
                        cases assump_55
                        case intro assump_57 assump_58 =>
                          have assump_692 : p5 := by
                            exact assump_57
                          let assump_68 := assump_41 assump_692
                          exact assump_68
                      case inr assump_56 =>
                        cases assump_56
                        case inl assump_70 =>
                          exact assump_70
                        case inr assump_71 =>
                          apply False.elim assump_71
                    case inr assump_52 =>
                      cases assump_52
                      case inl assump_76 =>
                        cases assump_50
                        case inl assump_80 =>
                          cases assump_80
                          case intro assump_82 assump_83 =>
                            have assump_693 : p5 := by
                              exact assump_82
                            let assump_92 := assump_41 assump_693
                            exact assump_92
                        case inr assump_81 =>
                          cases assump_81
                          case inl assump_94 =>
                            exact assump_94
                          case inr assump_95 =>
                            apply False.elim assump_95
                      case inr assump_77 =>
                        cases assump_50
                        case inl assump_102 =>
                          cases assump_102
                          case intro assump_104 assump_105 =>
                            have assump_694 : p5 := by
                              exact assump_104
                            let assump_114 := assump_41 assump_694
                            exact assump_114
                        case inr assump_103 =>
                          cases assump_103
                          case inl assump_116 =>
                            exact assump_116
                          case inr assump_117 =>
                            apply False.elim assump_117
                case inr assump_46 =>
                  cases assump_30
                  case intro assump_124 assump_125 =>
                    cases assump_124
                    case inl assump_126 =>
                      cases assump_125
                      case inl assump_130 =>
                        cases assump_130
                        case intro assump_132 assump_133 =>
                          have assump_695 : p5 := by
                            exact assump_132
                          let assump_143 := assump_41 assump_695
                          exact assump_143
                      case inr assump_131 =>
                        cases assump_131
                        case inl assump_145 =>
                          exact assump_145
                        case inr assump_146 =>
                          apply False.elim assump_146
                    case inr assump_127 =>
                      cases assump_127
                      case inl assump_151 =>
                        cases assump_125
                        case inl assump_155 =>
                          cases assump_155
                          case intro assump_157 assump_158 =>
                            have assump_696 : p5 := by
                              exact assump_157
                            let assump_167 := assump_41 assump_696
                            exact assump_167
                        case inr assump_156 =>
                          cases assump_156
                          case inl assump_169 =>
                            exact assump_169
                          case inr assump_170 =>
                            apply False.elim assump_170
                      case inr assump_152 =>
                        cases assump_125
                        case inl assump_177 =>
                          cases assump_177
                          case intro assump_179 assump_180 =>
                            have assump_697 : p5 := by
                              exact assump_179
                            let assump_189 := assump_41 assump_697
                            exact assump_189
                        case inr assump_178 =>
                          cases assump_178
                          case inl assump_191 =>
                            exact assump_191
                          case inr assump_192 =>
                            apply False.elim assump_192
  cases assump_12
  case intro assump_197 assump_198 =>
    cases assump_11
    case intro assump_203 assump_204 =>
      cases assump_203
      case intro assump_205 assump_206 =>
        cases assump_10
        case intro assump_213 assump_214 =>
          cases assump_213
          case intro assump_215 assump_216 =>
            cases assump_215
            case inl assump_217 =>
              cases assump_217
              case intro assump_219 assump_220 =>
                apply False.elim assump_219
            case inr assump_218 =>
              cases assump_216
              case intro assump_225 assump_226 =>
                cases assump_226
                case inl assump_229 =>
                  cases assump_214
                  case intro assump_233 assump_234 =>
                    cases assump_233
                    case inl assump_235 =>
                      cases assump_234
                      case inl assump_239 =>
                        cases assump_239
                        case intro assump_241 assump_242 =>
                          exact assump_206
                      case inr assump_240 =>
                        cases assump_240
                        case inl assump_247 =>
                          exact assump_206
                        case inr assump_248 =>
                          apply False.elim assump_248
                    case inr assump_236 =>
                      cases assump_236
                      case inl assump_253 =>
                        cases assump_234
                        case inl assump_257 =>
                          cases assump_257
                          case intro assump_259 assump_260 =>
                            exact assump_206
                        case inr assump_258 =>
                          cases assump_258
                          case inl assump_265 =>
                            exact assump_206
                          case inr assump_266 =>
                            apply False.elim assump_266
                      case inr assump_254 =>
                        cases assump_234
                        case inl assump_273 =>
                          cases assump_273
                          case intro assump_275 assump_276 =>
                            exact assump_206
                        case inr assump_274 =>
                          cases assump_274
                          case inl assump_281 =>
                            exact assump_206
                          case inr assump_282 =>
                            apply False.elim assump_282
                case inr assump_230 =>
                  cases assump_214
                  case intro assump_289 assump_290 =>
                    cases assump_289
                    case inl assump_291 =>
                      cases assump_290
                      case inl assump_295 =>
                        cases assump_295
                        case intro assump_297 assump_298 =>
                          exact assump_206
                      case inr assump_296 =>
                        cases assump_296
                        case inl assump_303 =>
                          exact assump_206
                        case inr assump_304 =>
                          apply False.elim assump_304
                    case inr assump_292 =>
                      cases assump_292
                      case inl assump_309 =>
                        cases assump_290
                        case inl assump_313 =>
                          cases assump_313
                          case intro assump_315 assump_316 =>
                            exact assump_206
                        case inr assump_314 =>
                          cases assump_314
                          case inl assump_321 =>
                            exact assump_206
                          case inr assump_322 =>
                            apply False.elim assump_322
                      case inr assump_310 =>
                        cases assump_290
                        case inl assump_329 =>
                          cases assump_329
                          case intro assump_331 assump_332 =>
                            exact assump_206
                        case inr assump_330 =>
                          cases assump_330
                          case inl assump_337 =>
                            exact assump_206
                          case inr assump_338 =>
                            apply False.elim assump_338
  apply And.intro
  intro assump_343
  intro assump_344
  cases assump_343
  case intro assump_347 assump_348 =>
    cases assump_10
    case intro assump_353 assump_354 =>
      cases assump_353
      case intro assump_355 assump_356 =>
        cases assump_355
        case inl assump_357 =>
          cases assump_357
          case intro assump_359 assump_360 =>
            apply False.elim assump_359
        case inr assump_358 =>
          cases assump_356
          case intro assump_365 assump_366 =>
            cases assump_366
            case inl assump_369 =>
              cases assump_354
              case intro assump_373 assump_374 =>
                cases assump_373
                case inl assump_375 =>
                  cases assump_374
                  case inl assump_379 =>
                    cases assump_379
                    case intro assump_381 assump_382 =>
                      exact assump_348
                  case inr assump_380 =>
                    cases assump_380
                    case inl assump_387 =>
                      exact assump_348
                    case inr assump_388 =>
                      apply False.elim assump_388
                case inr assump_376 =>
                  cases assump_376
                  case inl assump_393 =>
                    cases assump_374
                    case inl assump_397 =>
                      cases assump_397
                      case intro assump_399 assump_400 =>
                        exact assump_348
                    case inr assump_398 =>
                      cases assump_398
                      case inl assump_405 =>
                        exact assump_348
                      case inr assump_406 =>
                        apply False.elim assump_406
                  case inr assump_394 =>
                    cases assump_374
                    case inl assump_413 =>
                      cases assump_413
                      case intro assump_415 assump_416 =>
                        exact assump_348
                    case inr assump_414 =>
                      cases assump_414
                      case inl assump_421 =>
                        exact assump_348
                      case inr assump_422 =>
                        apply False.elim assump_422
            case inr assump_370 =>
              cases assump_354
              case intro assump_429 assump_430 =>
                cases assump_429
                case inl assump_431 =>
                  cases assump_430
                  case inl assump_435 =>
                    cases assump_435
                    case intro assump_437 assump_438 =>
                      exact assump_348
                  case inr assump_436 =>
                    cases assump_436
                    case inl assump_443 =>
                      exact assump_348
                    case inr assump_444 =>
                      apply False.elim assump_444
                case inr assump_432 =>
                  cases assump_432
                  case inl assump_449 =>
                    cases assump_430
                    case inl assump_453 =>
                      cases assump_453
                      case intro assump_455 assump_456 =>
                        exact assump_348
                    case inr assump_454 =>
                      cases assump_454
                      case inl assump_461 =>
                        exact assump_348
                      case inr assump_462 =>
                        apply False.elim assump_462
                  case inr assump_450 =>
                    cases assump_430
                    case inl assump_469 =>
                      cases assump_469
                      case intro assump_471 assump_472 =>
                        exact assump_348
                    case inr assump_470 =>
                      cases assump_470
                      case inl assump_477 =>
                        exact assump_348
                      case inr assump_478 =>
                        apply False.elim assump_478
  cases assump_10
  case intro assump_483 assump_484 =>
    cases assump_483
    case intro assump_485 assump_486 =>
      cases assump_485
      case inl assump_487 =>
        cases assump_487
        case intro assump_489 assump_490 =>
          apply False.elim assump_489
      case inr assump_488 =>
        cases assump_486
        case intro assump_495 assump_496 =>
          cases assump_496
          case inl assump_499 =>
            cases assump_484
            case intro assump_503 assump_504 =>
              cases assump_503
              case inl assump_505 =>
                cases assump_504
                case inl assump_509 =>
                  cases assump_509
                  case intro assump_511 assump_512 =>
                    apply Or.inl
                    intro assump_517
                    have assump_698 : p5 := by
                      exact assump_511
                    let assump_526 := assump_495 assump_698
                    exact assump_526
                case inr assump_510 =>
                  cases assump_510
                  case inl assump_528 =>
                    apply Or.inl
                    intro assump_532
                    exact assump_528
                  case inr assump_529 =>
                    apply False.elim assump_529
              case inr assump_506 =>
                cases assump_506
                case inl assump_537 =>
                  cases assump_504
                  case inl assump_541 =>
                    cases assump_541
                    case intro assump_543 assump_544 =>
                      apply Or.inl
                      intro assump_549
                      have assump_699 : p5 := by
                        exact assump_543
                      let assump_557 := assump_495 assump_699
                      exact assump_557
                  case inr assump_542 =>
                    cases assump_542
                    case inl assump_559 =>
                      apply Or.inl
                      intro assump_563
                      exact assump_559
                    case inr assump_560 =>
                      apply False.elim assump_560
                case inr assump_538 =>
                  cases assump_504
                  case inl assump_570 =>
                    cases assump_570
                    case intro assump_572 assump_573 =>
                      apply Or.inl
                      intro assump_578
                      have assump_700 : p5 := by
                        exact assump_572
                      let assump_586 := assump_495 assump_700
                      exact assump_586
                  case inr assump_571 =>
                    cases assump_571
                    case inl assump_588 =>
                      apply Or.inl
                      intro assump_592
                      exact assump_588
                    case inr assump_589 =>
                      apply False.elim assump_589
          case inr assump_500 =>
            cases assump_484
            case intro assump_599 assump_600 =>
              cases assump_599
              case inl assump_601 =>
                cases assump_600
                case inl assump_605 =>
                  cases assump_605
                  case intro assump_607 assump_608 =>
                    apply Or.inl
                    intro assump_613
                    have assump_701 : p5 := by
                      exact assump_607
                    let assump_621 := assump_495 assump_701
                    exact assump_621
                case inr assump_606 =>
                  cases assump_606
                  case inl assump_623 =>
                    apply Or.inl
                    intro assump_627
                    exact assump_623
                  case inr assump_624 =>
                    apply False.elim assump_624
              case inr assump_602 =>
                cases assump_602
                case inl assump_632 =>
                  cases assump_600
                  case inl assump_636 =>
                    cases assump_636
                    case intro assump_638 assump_639 =>
                      apply Or.inl
                      intro assump_644
                      have assump_702 : p5 := by
                        exact assump_638
                      let assump_652 := assump_495 assump_702
                      exact assump_652
                  case inr assump_637 =>
                    cases assump_637
                    case inl assump_654 =>
                      apply Or.inl
                      intro assump_658
                      exact assump_654
                    case inr assump_655 =>
                      apply False.elim assump_655
                case inr assump_633 =>
                  cases assump_600
                  case inl assump_665 =>
                    cases assump_665
                    case intro assump_667 assump_668 =>
                      apply Or.inl
                      intro assump_673
                      have assump_703 : p5 := by
                        exact assump_667
                      let assump_681 := assump_495 assump_703
                      exact assump_681
                  case inr assump_666 =>
                    cases assump_666
                    case inl assump_683 =>
                      apply Or.inl
                      intro assump_687
                      exact assump_683
                    case inr assump_684 =>
                      apply False.elim assump_684


variable (p4 p0 p6 p1 p5 p3 p7 : Prop)
theorem file25_55640 : (((((p6 → p7) ∧ (p5 ∨ p7)) ∧ ((True ∧ p0) → (p4 ∨ p3))) → False) → ((((p7 ∧ False) ∧ (True ∧ p1)) → False) ∨ (((p7 ∨ p0) ∧ (False ∨ p0)) ∨ ((True ∧ p4) → False)))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      apply False.elim assump_8


variable (p7 p2 p5 p1 p4 p0 p6 : Prop)
theorem file25_56060 : (((((p2 ∧ p2) → (p6 → False)) → False) → (((True ∨ p5) ∧ (False ∧ p4)) → False)) ∨ ((((False ∧ p6) → (p0 → p5)) ∧ ((False ∨ p6) → (False → False))) ∧ (((p7 → p5) → (p5 → True)) ∧ ((p6 → p1) ∨ (p5 ∧ p7))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_4
      case intro assump_9 assump_10 =>
        apply False.elim assump_9
    case inr assump_6 =>
      cases assump_4
      case intro assump_15 assump_16 =>
        apply False.elim assump_15


variable (p3 p5 p4 p0 p2 p6 p1 : Prop)
theorem file25_56694 : (((((p0 → p6) → False) → ((p3 ∧ p6) → False)) → (((p2 ∨ True) → False) ∧ ((p5 ∨ p2) → False))) → ((((p3 ∨ False) → False) → ((p5 → False) ∧ (False ∧ p5))) ∧ (((p2 ∨ p1) → False) ∨ ((p4 → p0) ∨ (p4 → p5))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  apply And.intro
  intro assump_3
  have assump_144 : (((p0 → p6) → False) → ((p3 ∧ p6) → False)) := by
    intro assump_11
    intro assump_12
    cases assump_12
    case intro assump_13 assump_14 =>
      have assump_145 : (p0 → p6) := by
        intro assump_22
        exact assump_14
      let assump_21 := assump_11 assump_145
      apply False.elim assump_21
  let assump_10 := assump_1 assump_144
  let assump_28 := And.left assump_10
  have assump_146 : (p2 ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_29 := assump_28 assump_146
  apply False.elim assump_29
  apply And.intro
  have assump_147 : (((p0 → p6) → False) → ((p3 ∧ p6) → False)) := by
    intro assump_38
    intro assump_39
    cases assump_39
    case intro assump_40 assump_41 =>
      have assump_148 : (p0 → p6) := by
        intro assump_49
        exact assump_41
      let assump_48 := assump_38 assump_148
      apply False.elim assump_48
  let assump_37 := assump_1 assump_147
  let assump_55 := And.left assump_37
  have assump_149 : (p2 ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_56 := assump_55 assump_149
  apply False.elim assump_56
  have assump_150 : (((p0 → p6) → False) → ((p3 ∧ p6) → False)) := by
    intro assump_65
    intro assump_66
    cases assump_66
    case intro assump_67 assump_68 =>
      have assump_151 : (p0 → p6) := by
        intro assump_76
        exact assump_68
      let assump_75 := assump_65 assump_151
      apply False.elim assump_75
  let assump_64 := assump_1 assump_150
  let assump_82 := And.left assump_64
  have assump_152 : (p2 ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_83 := assump_82 assump_152
  apply False.elim assump_83
  apply Or.inl
  intro assump_89
  cases assump_89
  case inl assump_90 =>
    have assump_153 : (((p0 → p6) → False) → ((p3 ∧ p6) → False)) := by
      intro assump_96
      intro assump_97
      cases assump_97
      case intro assump_98 assump_99 =>
        have assump_154 : (p0 → p6) := by
          intro assump_107
          exact assump_99
        let assump_106 := assump_96 assump_154
        apply False.elim assump_106
    let assump_95 := assump_1 assump_153
    let assump_113 := And.left assump_95
    have assump_155 : (p2 ∨ True) := by
      apply Or.inl
      exact assump_90
    let assump_114 := assump_113 assump_155
    apply False.elim assump_114
  case inr assump_91 =>
    have assump_156 : (((p0 → p6) → False) → ((p3 ∧ p6) → False)) := by
      intro assump_122
      intro assump_123
      cases assump_123
      case intro assump_124 assump_125 =>
        have assump_157 : (p0 → p6) := by
          intro assump_133
          exact assump_125
        let assump_132 := assump_122 assump_157
        apply False.elim assump_132
    let assump_121 := assump_1 assump_156
    let assump_139 := And.left assump_121
    have assump_158 : (p2 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_140 := assump_139 assump_158
    apply False.elim assump_140


variable (p6 p5 p4 p3 p2 p1 : Prop)
theorem file25_60036 : (((((p3 ∨ p4) → False) ∧ ((p1 ∧ False) ∧ (p6 ∨ p3))) → False) ∨ ((((p1 → False) ∨ (p6 → False)) ∧ ((p2 ∧ True) → (False → p4))) → (((False → p5) → (True ∧ p2)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_9


variable (p5 p1 p6 p7 : Prop)
theorem file25_60498 : (((((p5 ∧ True) ∧ (p6 → False)) → ((True ∨ p1) ∨ (p6 → False))) ∧ (((False → False) ∨ (p1 ∨ p7)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : ((False → False) ∨ (p1 ∨ p7)) := by
      apply Or.inl
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p3 p4 p6 p5 p2 p0 p1 : Prop)
theorem file25_60949 : ((((((p6 ∧ p5) ∨ (p6 ∨ p5)) ∧ ((p0 ∧ p4) ∨ (p1 → p2))) → (((p4 → p4) → False) → ((False ∧ p3) → False))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p6 ∧ p5) ∨ (p6 ∨ p5)) ∧ ((p0 ∧ p4) ∨ (p1 → p2))) → (((p4 → p4) → False) → ((False ∧ p3) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_7
    case intro assump_8 assump_9 =>
      apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p0 p7 p4 p5 p1 p6 p2 p3 : Prop)
theorem file25_61498 : (((((False ∧ p3) ∧ (p3 → False)) → ((p4 ∨ p7) → (p1 → False))) ∨ (((p3 → False) → False) ∧ ((p6 ∨ p2) → (p2 → False)))) ∨ ((((p3 → p5) → False) → False) ∨ (((p2 ∧ p1) → False) ∧ ((p0 → p1) ∨ (p1 → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_5
  intro assump_6
  intro assump_7
  cases assump_6
  case inl assump_10 =>
    cases assump_5
    case intro assump_14 assump_15 =>
      cases assump_14
      case intro assump_16 assump_17 =>
        apply False.elim assump_16
  case inr assump_11 =>
    cases assump_5
    case intro assump_22 assump_23 =>
      cases assump_22
      case intro assump_24 assump_25 =>
        apply False.elim assump_24


variable (p2 p5 p3 p1 : Prop)
theorem file25_62220 : ((((((False → p3) → (p2 → False)) → False) ∨ (((p5 → p5) ∧ (p3 → False)) ∧ ((p1 ∧ False) → False))) ∧ ((((p2 → False) ∧ (True → False)) → False) → False)) → False) := by
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    cases assump_10
    case inl assump_12 =>
      have assump_60 : (((p2 → False) ∧ (True → False)) → False) := by
        intro assump_19
        cases assump_19
        case intro assump_20 assump_21 =>
          have assump_61 : True := by
            apply True.intro
          let assump_26 := assump_21 assump_61
          apply False.elim assump_26
      let assump_18 := assump_11 assump_60
      apply False.elim assump_18
    case inr assump_13 =>
      cases assump_13
      case intro assump_33 assump_34 =>
        cases assump_33
        case intro assump_35 assump_36 =>
          have assump_62 : (((p2 → False) ∧ (True → False)) → False) := by
            intro assump_46
            cases assump_46
            case intro assump_47 assump_48 =>
              have assump_63 : True := by
                apply True.intro
              let assump_53 := assump_48 assump_63
              apply False.elim assump_53
          let assump_45 := assump_11 assump_62
          apply False.elim assump_45


variable (p5 p0 p7 p1 p3 p2 p6 p4 : Prop)
theorem file25_63542 : (((((p0 → p1) → False) ∧ ((p6 → False) ∧ (p4 ∧ False))) → (((p3 ∧ p2) ∧ (False ∨ p6)) ∨ ((p0 ∨ p5) → False))) ∨ ((((p6 → False) → False) ∨ ((p4 ∨ p3) → (False ∧ p2))) ∧ (((False ∧ p7) ∨ (False ∨ p6)) ∨ ((True ∧ p0) ∧ (False → p0))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        apply False.elim assump_11


variable (p1 p2 p4 p6 p7 p0 p5 p3 : Prop)
theorem file25_64082 : ((((((p7 ∨ p2) → (p5 ∧ p4)) → ((p3 → p3) ∨ (p1 → False))) → False) ∧ ((((True ∧ p2) → False) ∧ ((True ∨ p0) → (False → p5))) ∧ (((p0 → False) ∨ (p6 → False)) ∧ ((p1 ∧ p4) ∨ (p1 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case intro assump_14 assump_15 =>
          cases assump_14
          case inl assump_16 =>
            cases assump_15
            case inl assump_20 =>
              cases assump_20
              case intro assump_22 assump_23 =>
                have assump_104 : (((p7 ∨ p2) → (p5 ∧ p4)) → ((p3 → p3) ∨ (p1 → False))) := by
                  intro assump_35
                  apply Or.inl
                  intro assump_38
                  exact assump_38
                let assump_34 := assump_2 assump_104
                apply False.elim assump_34
            case inr assump_21 =>
              have assump_105 : (((p7 ∨ p2) → (p5 ∧ p4)) → ((p3 → p3) ∨ (p1 → False))) := by
                intro assump_52
                apply Or.inl
                intro assump_55
                exact assump_55
              let assump_51 := assump_2 assump_105
              apply False.elim assump_51
          case inr assump_17 =>
            cases assump_15
            case inl assump_63 =>
              cases assump_63
              case intro assump_65 assump_66 =>
                have assump_106 : (((p7 ∨ p2) → (p5 ∧ p4)) → ((p3 → p3) ∨ (p1 → False))) := by
                  intro assump_78
                  apply Or.inl
                  intro assump_81
                  exact assump_81
                let assump_77 := assump_2 assump_106
                apply False.elim assump_77
            case inr assump_64 =>
              have assump_107 : (((p7 ∨ p2) → (p5 ∧ p4)) → ((p3 → p3) ∨ (p1 → False))) := by
                intro assump_95
                apply Or.inl
                intro assump_98
                exact assump_98
              let assump_94 := assump_2 assump_107
              apply False.elim assump_94


variable (p0 p5 p6 p4 p1 p3 : Prop)
theorem file25_66300 : ((((((p1 ∨ True) → False) ∧ ((p0 → p3) ∧ (p6 ∨ p0))) → (((p5 → False) → (p3 ∨ p4)) → False)) → False) → False) := by
  intro assump_1
  have assump_39 : ((((p1 ∨ True) → False) ∧ ((p0 → p3) ∧ (p6 ∨ p0))) → (((p5 → False) → (p3 ∨ p4)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_10
      case intro assump_13 assump_14 =>
        cases assump_14
        case inl assump_17 =>
          have assump_40 : (p1 ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_23 := assump_9 assump_40
          apply False.elim assump_23
        case inr assump_18 =>
          have assump_41 : (p1 ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_32 := assump_9 assump_41
          apply False.elim assump_32
  let assump_4 := assump_1 assump_39
  apply False.elim assump_4


variable (p1 p6 p0 p5 p3 p7 p4 p2 : Prop)
theorem file25_67285 : (((((p0 → p3) → (p3 ∨ p6)) → ((p6 → p2) → False)) ∧ (((p6 → p4) → (p6 → False)) → False)) → ((((p5 ∨ p7) ∨ (p3 → False)) ∨ ((p3 → p5) → (p7 → False))) → (((p7 ∧ p1) → (False ∨ p4)) → ((False → False) ∨ (True ∨ p7))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    cases assump_6
    case inl assump_8 =>
      cases assump_8
      case inl assump_10 =>
        cases assump_1
        case intro assump_14 assump_15 =>
          apply Or.inl
          intro assump_20
          apply False.elim assump_20
      case inr assump_11 =>
        cases assump_1
        case intro assump_25 assump_26 =>
          apply Or.inl
          intro assump_31
          apply False.elim assump_31
    case inr assump_9 =>
      cases assump_1
      case intro assump_36 assump_37 =>
        apply Or.inl
        intro assump_42
        apply False.elim assump_42
  case inr assump_7 =>
    cases assump_1
    case intro assump_47 assump_48 =>
      apply Or.inl
      intro assump_53
      apply False.elim assump_53


variable (p4 p6 p7 p5 p2 p0 p3 p1 : Prop)
theorem file25_68409 : ((((((p1 → p4) → (p1 → p7)) → False) ∨ (((p5 → p2) ∨ (False → p1)) ∧ ((p3 → False) ∨ (False → True)))) ∧ ((((p7 → p4) ∧ (p7 ∨ p5)) → ((p7 → p0) ∧ (p7 ∧ True))) ∧ (((p5 → False) → (False → p5)) → ((False → False) ∧ (p6 ∧ False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        have assump_118 : ((p5 → False) → (False → p5)) := by
          intro assump_15
          intro assump_16
          apply False.elim assump_16
        let assump_14 := assump_9 assump_118
        let assump_19 := And.right assump_14
        let assump_21 := And.right assump_19
        apply False.elim assump_21
    case inr assump_5 =>
      cases assump_5
      case intro assump_26 assump_27 =>
        cases assump_26
        case inl assump_28 =>
          cases assump_27
          case inl assump_32 =>
            cases assump_3
            case intro assump_36 assump_37 =>
              have assump_119 : ((p5 → False) → (False → p5)) := by
                intro assump_43
                intro assump_44
                apply False.elim assump_44
              let assump_42 := assump_37 assump_119
              let assump_47 := And.right assump_42
              let assump_49 := And.right assump_47
              apply False.elim assump_49
          case inr assump_33 =>
            cases assump_3
            case intro assump_56 assump_57 =>
              have assump_120 : ((p5 → False) → (False → p5)) := by
                intro assump_63
                intro assump_64
                apply False.elim assump_64
              let assump_62 := assump_57 assump_120
              let assump_67 := And.right assump_62
              let assump_69 := And.right assump_67
              apply False.elim assump_69
        case inr assump_29 =>
          cases assump_27
          case inl assump_76 =>
            cases assump_3
            case intro assump_80 assump_81 =>
              have assump_121 : ((p5 → False) → (False → p5)) := by
                intro assump_87
                intro assump_88
                apply False.elim assump_88
              let assump_86 := assump_81 assump_121
              let assump_91 := And.right assump_86
              let assump_93 := And.right assump_91
              apply False.elim assump_93
          case inr assump_77 =>
            cases assump_3
            case intro assump_100 assump_101 =>
              have assump_122 : ((p5 → False) → (False → p5)) := by
                intro assump_107
                intro assump_108
                apply False.elim assump_108
              let assump_106 := assump_101 assump_122
              let assump_111 := And.right assump_106
              let assump_113 := And.right assump_111
              apply False.elim assump_113


variable (p0 p6 p1 p7 p2 p4 : Prop)
theorem file25_71341 : ((((((p2 ∧ p7) ∨ (p6 ∨ p0)) ∨ ((p7 → False) → False)) → (((True → False) → False) ∨ ((p4 ∧ p4) ∨ (p1 → p4)))) → False) → False) := by
  intro assump_14
  have assump_68 : ((((p2 ∧ p7) ∨ (p6 ∨ p0)) ∨ ((p7 → False) → False)) → (((True → False) → False) ∨ ((p4 ∧ p4) ∨ (p1 → p4)))) := by
    intro assump_18
    cases assump_18
    case inl assump_19 =>
      cases assump_19
      case inl assump_21 =>
        cases assump_21
        case intro assump_23 assump_24 =>
          apply Or.inl
          intro assump_29
          have assump_69 : True := by
            apply True.intro
          let assump_32 := assump_29 assump_69
          apply False.elim assump_32
      case inr assump_22 =>
        cases assump_22
        case inl assump_36 =>
          apply Or.inl
          intro assump_40
          have assump_70 : True := by
            apply True.intro
          let assump_43 := assump_40 assump_70
          apply False.elim assump_43
        case inr assump_37 =>
          apply Or.inl
          intro assump_49
          have assump_71 : True := by
            apply True.intro
          let assump_52 := assump_49 assump_71
          apply False.elim assump_52
    case inr assump_20 =>
      apply Or.inl
      intro assump_58
      have assump_72 : True := by
        apply True.intro
      let assump_61 := assump_58 assump_72
      apply False.elim assump_61
  let assump_17 := assump_14 assump_68
  apply False.elim assump_17


variable (p1 p7 p4 p3 p0 p5 p2 : Prop)
theorem file25_72853 : ((((((p1 ∧ False) → False) ∨ ((True ∨ p0) → False)) ∨ (((True ∨ p3) ∨ (p5 ∨ p2)) ∧ ((False ∧ False) → (p4 ∧ p7)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p1 ∧ False) → False) ∨ ((True ∨ p0) → False)) ∨ (((True ∨ p3) ∨ (p5 ∨ p2)) ∧ ((False ∧ False) → (p4 ∧ p7)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p1 p7 p0 p5 p4 p3 p2 : Prop)
theorem file25_73415 : ((((((p5 ∨ p3) ∨ (p0 → False)) → False) → False) ∧ ((((True ∨ p0) → (p4 ∧ True)) ∧ ((p5 ∧ False) ∧ (p7 → False))) ∧ (((p5 ∨ p4) ∨ (p2 → p1)) ∧ ((p7 → p7) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            apply False.elim assump_15


variable (p1 p0 p7 p3 p6 p2 : Prop)
theorem file25_74012 : (((((p1 ∨ True) ∧ (p7 ∧ False)) → ((p0 ∧ True) ∨ (p2 ∨ False))) → False) → ((((p7 → False) ∧ (p0 ∨ p3)) ∧ ((p1 → False) ∧ (p7 → False))) ∧ (((p6 ∨ p3) → False) → False))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  apply And.intro
  intro assump_2
  have assump_149 : (((p1 ∨ True) ∧ (p7 ∧ False)) → ((p0 ∧ True) ∨ (p2 ∨ False))) := by
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        cases assump_10
        case intro assump_15 assump_16 =>
          apply False.elim assump_16
      case inr assump_12 =>
        cases assump_10
        case intro assump_23 assump_24 =>
          apply False.elim assump_24
  let assump_7 := assump_1 assump_149
  apply False.elim assump_7
  have assump_150 : (((p1 ∨ True) ∧ (p7 ∧ False)) → ((p0 ∧ True) ∨ (p2 ∨ False))) := by
    intro assump_35
    cases assump_35
    case intro assump_36 assump_37 =>
      cases assump_36
      case inl assump_38 =>
        cases assump_37
        case intro assump_42 assump_43 =>
          apply False.elim assump_43
      case inr assump_39 =>
        cases assump_37
        case intro assump_50 assump_51 =>
          apply False.elim assump_51
  let assump_34 := assump_1 assump_150
  apply False.elim assump_34
  apply And.intro
  intro assump_59
  have assump_151 : (((p1 ∨ True) ∧ (p7 ∧ False)) → ((p0 ∧ True) ∨ (p2 ∨ False))) := by
    intro assump_65
    cases assump_65
    case intro assump_66 assump_67 =>
      cases assump_66
      case inl assump_68 =>
        cases assump_67
        case intro assump_72 assump_73 =>
          apply False.elim assump_73
      case inr assump_69 =>
        cases assump_67
        case intro assump_80 assump_81 =>
          apply False.elim assump_81
  let assump_64 := assump_1 assump_151
  apply False.elim assump_64
  intro assump_89
  have assump_152 : (((p1 ∨ True) ∧ (p7 ∧ False)) → ((p0 ∧ True) ∨ (p2 ∨ False))) := by
    intro assump_95
    cases assump_95
    case intro assump_96 assump_97 =>
      cases assump_96
      case inl assump_98 =>
        cases assump_97
        case intro assump_102 assump_103 =>
          apply False.elim assump_103
      case inr assump_99 =>
        cases assump_97
        case intro assump_110 assump_111 =>
          apply False.elim assump_111
  let assump_94 := assump_1 assump_152
  apply False.elim assump_94
  intro assump_119
  have assump_153 : (((p1 ∨ True) ∧ (p7 ∧ False)) → ((p0 ∧ True) ∨ (p2 ∨ False))) := by
    intro assump_125
    cases assump_125
    case intro assump_126 assump_127 =>
      cases assump_126
      case inl assump_128 =>
        cases assump_127
        case intro assump_132 assump_133 =>
          apply False.elim assump_133
      case inr assump_129 =>
        cases assump_127
        case intro assump_140 assump_141 =>
          apply False.elim assump_141
  let assump_124 := assump_1 assump_153
  apply False.elim assump_124


variable (p1 p4 p2 p5 p7 : Prop)
theorem file25_77014 : ((((((False ∧ p1) → (p7 ∧ p2)) → False) → (((p4 → False) ∨ (p5 → False)) → ((p7 ∨ False) ∨ (p1 → p1)))) → False) → False) := by
  intro assump_1
  have assump_26 : ((((False ∧ p1) → (p7 ∧ p2)) → False) → (((p4 → False) ∨ (p5 → False)) → ((p7 ∨ False) ∨ (p1 → p1)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      apply Or.inr
      intro assump_13
      exact assump_13
    case inr assump_8 =>
      apply Or.inr
      intro assump_20
      exact assump_20
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p6 p5 p1 p4 p2 : Prop)
theorem file25_77641 : ((((((p5 ∨ p4) ∨ (p2 ∧ p4)) → ((p5 ∨ p4) ∨ (p4 ∨ p1))) ∧ (((p5 ∨ True) ∨ (True → False)) ∨ ((True ∨ p2) ∨ (p4 ∨ p6)))) → False) → False) := by
  intro assump_1
  have assump_23 : ((((p5 ∨ p4) ∨ (p2 ∧ p4)) → ((p5 ∨ p4) ∨ (p4 ∨ p1))) ∧ (((p5 ∨ True) ∨ (True → False)) ∨ ((True ∨ p2) ∨ (p4 ∨ p6)))) := by
    apply And.intro
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        apply Or.inl
        apply Or.inl
        exact assump_8
      case inr assump_9 =>
        apply Or.inl
        apply Or.inr
        exact assump_9
    case inr assump_7 =>
      cases assump_7
      case intro assump_14 assump_15 =>
        apply Or.inl
        apply Or.inr
        exact assump_15
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p1 p7 p2 p3 p4 p0 : Prop)
theorem file25_78580 : ((((((p4 → False) ∨ (p7 → False)) → ((p2 ∧ p2) ∧ (p0 → False))) → (((p3 ∧ False) → (p0 ∧ p1)) → ((p3 ∧ False) → False))) → False) → False) := by
  intro assump_1
  have assump_17 : ((((p4 → False) ∨ (p7 → False)) → ((p2 ∧ p2) ∧ (p0 → False))) → (((p3 ∧ False) → (p0 ∧ p1)) → ((p3 ∧ False) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_7
    case intro assump_8 assump_9 =>
      apply False.elim assump_9
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p0 p5 p1 p6 p2 p3 p4 p7 : Prop)
theorem file25_79161 : (((((p4 → p7) ∧ (False ∧ p6)) → ((p5 → False) → False)) ∧ (((True ∧ p6) ∨ (True → False)) ∧ ((p1 → p1) → False))) → ((((True ∧ p3) ∧ (p1 ∨ True)) → ((p3 ∧ p2) ∧ (p6 ∨ p5))) ∧ (((p5 → p3) ∨ (p0 → p7)) → ((False → p0) → (p1 → p7))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  apply And.intro
  apply And.intro
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_4
      case inl assump_11 =>
        cases assump_1
        case intro assump_15 assump_16 =>
          cases assump_16
          case intro assump_19 assump_20 =>
            cases assump_19
            case inl assump_21 =>
              cases assump_21
              case intro assump_23 assump_24 =>
                exact assump_6
            case inr assump_22 =>
              exact assump_6
      case inr assump_12 =>
        cases assump_1
        case intro assump_37 assump_38 =>
          cases assump_38
          case intro assump_41 assump_42 =>
            cases assump_41
            case inl assump_43 =>
              cases assump_43
              case intro assump_45 assump_46 =>
                exact assump_6
            case inr assump_44 =>
              exact assump_6
  cases assump_2
  case intro assump_57 assump_58 =>
    cases assump_57
    case intro assump_59 assump_60 =>
      cases assump_58
      case inl assump_65 =>
        cases assump_1
        case intro assump_69 assump_70 =>
          cases assump_70
          case intro assump_73 assump_74 =>
            cases assump_73
            case inl assump_75 =>
              cases assump_75
              case intro assump_77 assump_78 =>
                have assump_288 : (p1 → p1) := by
                  intro assump_86
                  exact assump_86
                let assump_85 := assump_74 assump_288
                apply False.elim assump_85
            case inr assump_76 =>
              have assump_289 : (p1 → p1) := by
                intro assump_97
                exact assump_97
              let assump_96 := assump_74 assump_289
              apply False.elim assump_96
      case inr assump_66 =>
        cases assump_1
        case intro assump_105 assump_106 =>
          cases assump_106
          case intro assump_109 assump_110 =>
            cases assump_109
            case inl assump_111 =>
              cases assump_111
              case intro assump_113 assump_114 =>
                have assump_290 : (p1 → p1) := by
                  intro assump_122
                  exact assump_122
                let assump_121 := assump_110 assump_290
                apply False.elim assump_121
            case inr assump_112 =>
              have assump_291 : (p1 → p1) := by
                intro assump_133
                exact assump_133
              let assump_132 := assump_110 assump_291
              apply False.elim assump_132
  cases assump_2
  case intro assump_139 assump_140 =>
    cases assump_139
    case intro assump_141 assump_142 =>
      cases assump_140
      case inl assump_147 =>
        cases assump_1
        case intro assump_151 assump_152 =>
          cases assump_152
          case intro assump_155 assump_156 =>
            cases assump_155
            case inl assump_157 =>
              cases assump_157
              case intro assump_159 assump_160 =>
                apply Or.inl
                exact assump_160
            case inr assump_158 =>
              have assump_292 : (p1 → p1) := by
                intro assump_172
                exact assump_172
              let assump_171 := assump_156 assump_292
              apply False.elim assump_171
      case inr assump_148 =>
        cases assump_1
        case intro assump_180 assump_181 =>
          cases assump_181
          case intro assump_184 assump_185 =>
            cases assump_184
            case inl assump_186 =>
              cases assump_186
              case intro assump_188 assump_189 =>
                apply Or.inl
                exact assump_189
            case inr assump_187 =>
              have assump_293 : (p1 → p1) := by
                intro assump_201
                exact assump_201
              let assump_200 := assump_185 assump_293
              apply False.elim assump_200
  intro assump_207
  intro assump_208
  intro assump_209
  cases assump_207
  case inl assump_214 =>
    cases assump_1
    case intro assump_218 assump_219 =>
      cases assump_219
      case intro assump_222 assump_223 =>
        cases assump_222
        case inl assump_224 =>
          cases assump_224
          case intro assump_226 assump_227 =>
            have assump_294 : (p1 → p1) := by
              intro assump_235
              exact assump_235
            let assump_234 := assump_223 assump_294
            apply False.elim assump_234
        case inr assump_225 =>
          have assump_295 : (p1 → p1) := by
            intro assump_246
            exact assump_246
          let assump_245 := assump_223 assump_295
          apply False.elim assump_245
  case inr assump_215 =>
    cases assump_1
    case intro assump_254 assump_255 =>
      cases assump_255
      case intro assump_258 assump_259 =>
        cases assump_258
        case inl assump_260 =>
          cases assump_260
          case intro assump_262 assump_263 =>
            have assump_296 : (p1 → p1) := by
              intro assump_271
              exact assump_271
            let assump_270 := assump_259 assump_296
            apply False.elim assump_270
        case inr assump_261 =>
          have assump_297 : (p1 → p1) := by
            intro assump_282
            exact assump_282
          let assump_281 := assump_259 assump_297
          apply False.elim assump_281


variable (p0 p1 p5 p7 p4 : Prop)
theorem file25_84988 : ((((((p1 → False) ∧ (p0 ∧ p1)) ∨ ((False → p7) → (p7 → False))) → False) ∧ ((((p7 ∨ p5) → (p7 → p4)) → False) ∧ (((False → p7) → False) ∧ ((False → False) ∧ (p0 → p5))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          have assump_29 : (False → p7) := by
            intro assump_23
            apply False.elim assump_23
          let assump_22 := assump_10 assump_29
          apply False.elim assump_22


variable (p2 p0 p4 p7 p3 p1 : Prop)
theorem file25_85681 : (((((p2 ∨ False) ∧ (True → False)) → False) ∨ (((p2 → False) → (p1 → p7)) ∧ ((p4 → True) ∧ (True ∨ p7)))) ∧ ((((p3 ∨ p2) ∧ (True → p3)) ∧ ((p0 ∨ False) ∧ (True → False))) → False)) := by
  apply And.intro
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_59 : True := by
        apply True.intro
      let assump_10 := assump_3 assump_59
      apply False.elim assump_10
    case inr assump_5 =>
      apply False.elim assump_5
  intro assump_16
  cases assump_16
  case intro assump_17 assump_18 =>
    cases assump_17
    case intro assump_19 assump_20 =>
      cases assump_19
      case inl assump_21 =>
        cases assump_18
        case intro assump_27 assump_28 =>
          cases assump_27
          case inl assump_29 =>
            have assump_60 : True := by
              apply True.intro
            let assump_35 := assump_28 assump_60
            apply False.elim assump_35
          case inr assump_30 =>
            apply False.elim assump_30
      case inr assump_22 =>
        cases assump_18
        case intro assump_45 assump_46 =>
          cases assump_45
          case inl assump_47 =>
            have assump_61 : True := by
              apply True.intro
            let assump_53 := assump_46 assump_61
            apply False.elim assump_53
          case inr assump_48 =>
            apply False.elim assump_48


variable (p0 p7 p4 p5 : Prop)
theorem file25_87174 : (((((p0 → True) ∧ (p0 ∧ p7)) ∨ ((p4 ∧ p5) → (False → p5))) → False) → False) := by
  intro assump_1
  have assump_13 : (((p0 → True) ∧ (p0 ∧ p7)) ∨ ((p4 ∧ p5) → (False → p5))) := by
    apply Or.inr
    intro assump_6
    intro assump_7
    apply False.elim assump_7
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p0 p7 p3 : Prop)
theorem file25_87557 : ((((((p0 ∧ p7) ∧ (p0 → False)) ∨ ((False ∨ p0) → False)) → (((p3 ∧ p0) ∧ (p7 ∧ p3)) → False)) → False) → False) := by
  intro assump_1
  have assump_46 : ((((p0 ∧ p7) ∧ (p0 → False)) ∨ ((False ∨ p0) → False)) → (((p3 ∧ p0) ∧ (p7 ∧ p3)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_8
        case intro assump_15 assump_16 =>
          cases assump_5
          case inl assump_21 =>
            cases assump_21
            case intro assump_23 assump_24 =>
              cases assump_23
              case intro assump_25 assump_26 =>
                have assump_47 : p0 := by
                  exact assump_25
                let assump_33 := assump_24 assump_47
                apply False.elim assump_33
          case inr assump_22 =>
            have assump_48 : (False ∨ p0) := by
              apply Or.inr
              exact assump_10
            let assump_39 := assump_22 assump_48
            apply False.elim assump_39
  let assump_4 := assump_1 assump_46
  apply False.elim assump_4


variable (p6 p7 p0 p4 p3 : Prop)
theorem file25_88755 : ((((((True ∨ p6) → False) → ((p7 ∧ p3) → (p4 ∨ p0))) → (((p7 → False) → (p0 → False)) → ((p0 ∧ False) → False))) → False) → False) := by
  intro assump_1
  have assump_17 : ((((True ∨ p6) → False) → ((p7 ∧ p3) → (p4 ∨ p0))) → (((p7 → False) → (p0 → False)) → ((p0 ∧ False) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_7
    case intro assump_8 assump_9 =>
      apply False.elim assump_9
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p1 p6 p2 p4 : Prop)
theorem file25_89308 : ((((((p6 ∧ p2) → False) ∧ ((p1 → p4) → False)) → (((p4 ∧ True) ∧ (True → False)) → ((p1 ∧ False) → (True ∨ False)))) → False) → False) := by
  intro assump_1
  have assump_17 : ((((p6 ∧ p2) → False) ∧ ((p1 → p4) → False)) → (((p4 ∧ True) ∧ (True → False)) → ((p1 ∧ False) → (True ∨ False)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_7
    case intro assump_8 assump_9 =>
      apply False.elim assump_9
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p5 p3 p0 p4 p2 p7 : Prop)
theorem file25_89875 : ((((((p4 ∧ p7) ∨ (False → False)) → ((p0 → p5) ∧ (p2 → p7))) ∨ (((p7 → False) ∧ (True → True)) → ((p3 ∨ p3) ∨ (p5 ∧ False)))) ∧ ((((False → False) → (True → False)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_44 : (((False → False) → (True → False)) → False) := by
        intro assump_11
        have assump_45 : (False → False) := by
          intro assump_15
          apply False.elim assump_15
        let assump_14 := assump_11 assump_45
        have assump_46 : True := by
          apply True.intro
        let assump_18 := assump_14 assump_46
        apply False.elim assump_18
      let assump_10 := assump_3 assump_44
      apply False.elim assump_10
    case inr assump_5 =>
      have assump_47 : (((False → False) → (True → False)) → False) := by
        intro assump_30
        have assump_48 : (False → False) := by
          intro assump_34
          apply False.elim assump_34
        let assump_33 := assump_30 assump_48
        have assump_49 : True := by
          apply True.intro
        let assump_37 := assump_33 assump_49
        apply False.elim assump_37
      let assump_29 := assump_3 assump_47
      apply False.elim assump_29


variable (p2 p0 p5 p7 p3 p1 p4 : Prop)
theorem file25_91216 : ((((((p1 ∨ p4) → (p2 ∧ False)) ∧ ((p5 ∧ p4) ∧ (p3 → p2))) ∨ (((p4 → p2) ∨ (p3 → False)) ∧ ((p4 → False) ∨ (p1 ∧ True)))) ∧ ((((False → False) → (p5 ∧ p0)) ∧ ((p2 ∧ False) ∧ (p5 ∨ p1))) ∧ (((p7 ∨ p5) ∧ (p7 → p3)) → ((p2 ∨ p5) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            cases assump_3
            case intro assump_20 assump_21 =>
              cases assump_20
              case intro assump_22 assump_23 =>
                cases assump_23
                case intro assump_26 assump_27 =>
                  cases assump_26
                  case intro assump_28 assump_29 =>
                    apply False.elim assump_29
    case inr assump_5 =>
      cases assump_5
      case intro assump_34 assump_35 =>
        cases assump_34
        case inl assump_36 =>
          cases assump_35
          case inl assump_40 =>
            cases assump_3
            case intro assump_44 assump_45 =>
              cases assump_44
              case intro assump_46 assump_47 =>
                cases assump_47
                case intro assump_50 assump_51 =>
                  cases assump_50
                  case intro assump_52 assump_53 =>
                    apply False.elim assump_53
          case inr assump_41 =>
            cases assump_41
            case intro assump_58 assump_59 =>
              cases assump_3
              case intro assump_64 assump_65 =>
                cases assump_64
                case intro assump_66 assump_67 =>
                  cases assump_67
                  case intro assump_70 assump_71 =>
                    cases assump_70
                    case intro assump_72 assump_73 =>
                      apply False.elim assump_73
        case inr assump_37 =>
          cases assump_35
          case inl assump_80 =>
            cases assump_3
            case intro assump_84 assump_85 =>
              cases assump_84
              case intro assump_86 assump_87 =>
                cases assump_87
                case intro assump_90 assump_91 =>
                  cases assump_90
                  case intro assump_92 assump_93 =>
                    apply False.elim assump_93
          case inr assump_81 =>
            cases assump_81
            case intro assump_98 assump_99 =>
              cases assump_3
              case intro assump_104 assump_105 =>
                cases assump_104
                case intro assump_106 assump_107 =>
                  cases assump_107
                  case intro assump_110 assump_111 =>
                    cases assump_110
                    case intro assump_112 assump_113 =>
                      apply False.elim assump_113


variable (p2 p7 p3 p5 p4 p6 p1 : Prop)
theorem file25_94213 : (((((p7 ∧ p2) → False) → ((p5 → False) → False)) → False) → ((((p2 ∧ p7) ∧ (p4 ∧ p1)) ∧ ((p6 → p3) ∨ (p1 → False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        cases assump_6
        case intro assump_13 assump_14 =>
          cases assump_4
          case inl assump_19 =>
            have assump_57 : (((p7 ∧ p2) → False) → ((p5 → False) → False)) := by
              intro assump_26
              intro assump_27
              have assump_58 : (p7 ∧ p2) := by
                apply And.intro
                exact assump_8
                exact assump_7
              let assump_32 := assump_26 assump_58
              apply False.elim assump_32
            let assump_25 := assump_1 assump_57
            apply False.elim assump_25
          case inr assump_20 =>
            have assump_59 : (((p7 ∧ p2) → False) → ((p5 → False) → False)) := by
              intro assump_44
              intro assump_45
              have assump_60 : (p7 ∧ p2) := by
                apply And.intro
                exact assump_8
                exact assump_7
              let assump_50 := assump_44 assump_60
              apply False.elim assump_50
            let assump_43 := assump_1 assump_59
            apply False.elim assump_43


variable (p7 p3 p6 : Prop)
theorem file25_95673 : (((((True → False) ∧ (p3 → False)) → ((p7 → p3) → False)) → (((True → False) → (p6 ∧ False)) → False)) → False) := by
  intro assump_1
  have assump_37 : (((True → False) ∧ (p3 → False)) → ((p7 → p3) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      have assump_38 : True := by
        apply True.intro
      let assump_16 := assump_9 assump_38
      apply False.elim assump_16
  let assump_4 := assump_1 assump_37
  have assump_39 : ((True → False) → (p6 ∧ False)) := by
    intro assump_21
    apply And.intro
    have assump_40 : True := by
      apply True.intro
    let assump_24 := assump_21 assump_40
    apply False.elim assump_24
    have assump_41 : True := by
      apply True.intro
    let assump_30 := assump_21 assump_41
    apply False.elim assump_30
  let assump_20 := assump_4 assump_39
  apply False.elim assump_20


variable (p1 p3 p6 p5 p7 p2 p4 : Prop)
theorem file25_96635 : ((((((p2 → p1) → False) ∧ ((p2 ∧ p5) → (p1 → p1))) → False) ∧ ((((False → p4) ∧ (p6 → False)) ∧ ((p3 ∧ False) ∧ (p7 ∧ False))) ∧ (((p3 → p1) ∧ (True ∧ p5)) ∧ ((p6 ∨ p6) ∧ (True ∧ p2))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_9
          case intro assump_16 assump_17 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              apply False.elim assump_19


variable (p3 p6 p7 p0 p2 p5 p4 : Prop)
theorem file25_97331 : (((((p3 → p4) ∨ (False → False)) ∨ ((p5 → False) → False)) → False) → ((((p3 → False) → (False → False)) ∨ ((p4 → p6) → (p7 → False))) ∨ (((p0 → False) ∧ (True ∧ False)) ∧ ((p2 → False) ∨ (p5 → False))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  intro assump_5
  apply False.elim assump_5


variable (p1 p4 p6 p7 p5 p2 p0 : Prop)
theorem file25_97714 : ((((((p6 ∧ p0) ∧ (True ∧ p2)) → False) → False) ∧ ((((p7 → p7) → False) ∧ ((True → False) ∨ (p4 → p0))) ∨ (((p5 ∧ p2) ∨ (False ∧ p0)) ∧ ((p2 ∨ p1) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case inl assump_12 =>
          have assump_50 : True := by
            apply True.intro
          let assump_16 := assump_12 assump_50
          apply False.elim assump_16
        case inr assump_13 =>
          have assump_51 : (p7 → p7) := by
            intro assump_24
            exact assump_24
          let assump_23 := assump_8 assump_51
          apply False.elim assump_23
    case inr assump_7 =>
      cases assump_7
      case intro assump_30 assump_31 =>
        cases assump_30
        case inl assump_32 =>
          cases assump_32
          case intro assump_34 assump_35 =>
            have assump_52 : (p2 ∨ p1) := by
              apply Or.inl
              exact assump_35
            let assump_42 := assump_31 assump_52
            apply False.elim assump_42
        case inr assump_33 =>
          cases assump_33
          case intro assump_46 assump_47 =>
            apply False.elim assump_46


variable (p5 p3 p7 p0 p2 p1 : Prop)
theorem file25_99074 : ((((((p5 → False) ∨ (p3 → False)) ∧ ((p2 → p1) ∧ (p0 → False))) ∨ (((False → False) → False) → False)) ∧ ((((False → False) → (False ∨ True)) ∨ ((True ∧ p3) ∨ (p3 → p7))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_7
          case intro assump_12 assump_13 =>
            have assump_55 : (((False → False) → (False ∨ True)) ∨ ((True ∧ p3) ∨ (p3 → p7))) := by
              apply Or.inl
              intro assump_21
              apply Or.inr
              apply True.intro
            let assump_20 := assump_3 assump_55
            apply False.elim assump_20
        case inr assump_9 =>
          cases assump_7
          case intro assump_29 assump_30 =>
            have assump_56 : (((False → False) → (False ∨ True)) ∨ ((True ∧ p3) ∨ (p3 → p7))) := by
              apply Or.inl
              intro assump_38
              apply Or.inr
              apply True.intro
            let assump_37 := assump_3 assump_56
            apply False.elim assump_37
    case inr assump_5 =>
      have assump_57 : (((False → False) → (False ∨ True)) ∨ ((True ∧ p3) ∨ (p3 → p7))) := by
        apply Or.inl
        intro assump_49
        apply Or.inr
        apply True.intro
      let assump_48 := assump_3 assump_57
      apply False.elim assump_48


variable (p7 p2 p5 p1 p0 p4 p3 : Prop)
theorem file25_100612 : (((((p4 ∨ p3) ∨ (False → True)) → ((p0 ∧ False) → False)) ∨ (((p1 ∨ p4) → False) → ((p3 ∧ p2) ∨ (p5 ∨ p1)))) ∨ ((((p2 → False) → False) ∨ ((p2 ∧ p7) ∧ (False ∨ p2))) ∨ (((True ∧ p5) → False) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    apply False.elim assump_4


variable (p2 p7 p5 p1 : Prop)
theorem file25_101019 : ((((((p2 → False) ∧ (p1 ∨ p2)) → ((True ∧ p5) ∧ (p7 ∨ True))) → False) ∧ ((((False → False) ∨ (p2 → False)) ∨ ((p7 ∨ p2) → (False → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : (((False → False) ∨ (p2 → False)) ∨ ((p7 ∨ p2) → (False → False))) := by
      apply Or.inl
      apply Or.inl
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p3 p1 p7 p4 p0 p6 p2 : Prop)
theorem file25_101570 : ((((((True ∧ p4) → (p3 ∨ p4)) ∨ ((p4 → p6) → False)) ∨ (((p0 ∨ p6) ∧ (p3 ∧ p7)) → ((p3 ∨ p2) ∨ (p1 ∧ p7)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((True ∧ p4) → (p3 ∨ p4)) ∨ ((p4 → p6) → False)) ∨ (((p0 ∨ p6) ∧ (p3 ∧ p7)) → ((p3 ∨ p2) ∨ (p1 ∧ p7)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inr
      exact assump_7
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p3 p7 p4 p1 p6 p2 : Prop)
theorem file25_102123 : (((((p7 → False) → False) ∧ ((p2 → p6) → (p1 → False))) ∧ (((p6 ∧ False) → False) ∧ ((p4 → False) ∧ (p4 ∧ p4)))) → ((((False ∨ p3) ∨ (p7 → False)) ∨ ((False → p1) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_5
      case inl assump_7 =>
        apply False.elim assump_7
      case inr assump_8 =>
        cases assump_1
        case intro assump_13 assump_14 =>
          cases assump_13
          case intro assump_15 assump_16 =>
            cases assump_14
            case intro assump_21 assump_22 =>
              cases assump_22
              case intro assump_25 assump_26 =>
                cases assump_26
                case intro assump_29 assump_30 =>
                  have assump_101 : p4 := by
                    exact assump_30
                  let assump_37 := assump_25 assump_101
                  apply False.elim assump_37
    case inr assump_6 =>
      cases assump_1
      case intro assump_43 assump_44 =>
        cases assump_43
        case intro assump_45 assump_46 =>
          cases assump_44
          case intro assump_51 assump_52 =>
            cases assump_52
            case intro assump_55 assump_56 =>
              cases assump_56
              case intro assump_59 assump_60 =>
                have assump_102 : p4 := by
                  exact assump_60
                let assump_67 := assump_55 assump_102
                apply False.elim assump_67
  case inr assump_4 =>
    cases assump_1
    case intro assump_73 assump_74 =>
      cases assump_73
      case intro assump_75 assump_76 =>
        cases assump_74
        case intro assump_81 assump_82 =>
          cases assump_82
          case intro assump_85 assump_86 =>
            cases assump_86
            case intro assump_89 assump_90 =>
              have assump_103 : p4 := by
                exact assump_90
              let assump_97 := assump_85 assump_103
              apply False.elim assump_97


variable (p3 p6 p0 p5 p2 p7 : Prop)
theorem file25_104216 : ((((((True ∨ p2) ∨ (True → False)) ∨ ((p0 ∨ p3) ∧ (p2 ∨ p5))) ∨ (((p7 ∧ p6) → (True → p7)) → False)) → False) → False) := by
  intro assump_1
  have assump_8 : ((((True ∨ p2) ∨ (True → False)) ∨ ((p0 ∨ p3) ∧ (p2 ∨ p5))) ∨ (((p7 ∧ p6) → (True → p7)) → False)) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p3 p0 p5 p2 p1 p4 : Prop)
theorem file25_104694 : (((((p3 → p1) ∨ (p3 → False)) → ((False → True) → False)) ∨ (((True ∧ p5) → (p4 → p4)) ∨ ((p0 → p4) ∧ (p0 ∨ p1)))) → ((((False ∨ False) ∧ (p4 → False)) ∧ ((p2 → p1) → (True → False))) → False)) := by
  intro assump_5
  intro assump_6
  cases assump_6
  case intro assump_7 assump_8 =>
    cases assump_7
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        apply False.elim assump_11
      case inr assump_12 =>
        apply False.elim assump_12


variable (p4 p7 p5 p2 p0 p6 p3 p1 : Prop)
theorem file25_105248 : (((((p1 ∧ True) ∧ (p3 → p5)) ∨ ((p2 ∧ False) → (False → p5))) ∨ (((p4 ∧ p5) ∨ (p0 → False)) ∧ ((p6 ∨ p3) → False))) ∨ ((((p4 → False) → (p2 ∧ p6)) ∧ ((p7 ∧ p3) → (p2 → False))) ∧ (((p7 → False) ∨ (p5 ∧ p4)) → False))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inr
  intro assump_1
  intro assump_2
  apply False.elim assump_2


variable (p2 p0 p4 p6 p5 p3 : Prop)
theorem file25_105639 : (((((p6 → p5) ∨ (p0 ∧ p6)) → ((False → False) → False)) → (((p5 → False) → (False → p6)) ∨ ((True ∧ p5) → False))) ∨ ((((p5 → False) → False) ∨ ((p5 ∧ False) ∧ (p2 → p2))) ∧ (((p3 ∧ p4) ∨ (True → False)) → ((True → False) → False)))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  apply False.elim assump_5


variable (p4 p1 p0 p6 p7 p2 : Prop)
theorem file25_106048 : (((((p4 ∨ p2) ∧ (p6 ∨ p0)) ∨ ((p7 ∨ p1) → (p1 ∨ False))) ∧ (((p6 ∧ False) → False) → False)) → ((((p2 → False) → False) → ((False → False) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_9
        case inl assump_11 =>
          cases assump_10
          case inl assump_15 =>
            have assump_96 : ((p6 ∧ False) → False) := by
              intro assump_22
              cases assump_22
              case intro assump_23 assump_24 =>
                apply False.elim assump_24
            let assump_21 := assump_6 assump_96
            apply False.elim assump_21
          case inr assump_16 =>
            have assump_97 : ((p6 ∧ False) → False) := by
              intro assump_37
              cases assump_37
              case intro assump_38 assump_39 =>
                apply False.elim assump_39
            let assump_36 := assump_6 assump_97
            apply False.elim assump_36
        case inr assump_12 =>
          cases assump_10
          case inl assump_49 =>
            have assump_98 : ((p6 ∧ False) → False) := by
              intro assump_56
              cases assump_56
              case intro assump_57 assump_58 =>
                apply False.elim assump_58
            let assump_55 := assump_6 assump_98
            apply False.elim assump_55
          case inr assump_50 =>
            have assump_99 : ((p6 ∧ False) → False) := by
              intro assump_71
              cases assump_71
              case intro assump_72 assump_73 =>
                apply False.elim assump_73
            let assump_70 := assump_6 assump_99
            apply False.elim assump_70
    case inr assump_8 =>
      have assump_100 : ((p6 ∧ False) → False) := by
        intro assump_86
        cases assump_86
        case intro assump_87 assump_88 =>
          apply False.elim assump_88
      let assump_85 := assump_6 assump_100
      apply False.elim assump_85


variable (p6 p4 p0 p1 p3 p2 p7 p5 : Prop)
theorem file25_108196 : (((((p2 ∨ p5) ∨ (True ∧ p5)) ∧ ((p6 ∨ p0) ∧ (p0 → False))) → (((p6 ∨ False) ∧ (p5 ∨ p2)) ∨ ((True → p5) ∧ (p5 → p4)))) ∨ ((((p3 → p7) ∨ (p4 ∧ p1)) ∧ ((p7 → p2) ∨ (False ∧ p2))) → (((p3 ∨ True) ∧ (False → p2)) → False))) := by
  apply Or.inl
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case inl assump_8 =>
      cases assump_8
      case inl assump_10 =>
        cases assump_7
        case intro assump_14 assump_15 =>
          cases assump_14
          case inl assump_16 =>
            apply Or.inl
            apply And.intro
            apply Or.inl
            exact assump_16
            apply Or.inr
            exact assump_10
          case inr assump_17 =>
            apply Or.inr
            apply And.intro
            intro assump_26
            have assump_95 : p0 := by
              exact assump_17
            let assump_29 := assump_15 assump_95
            apply False.elim assump_29
            intro assump_33
            have assump_96 : p0 := by
              exact assump_17
            let assump_37 := assump_15 assump_96
            apply False.elim assump_37
      case inr assump_11 =>
        cases assump_7
        case intro assump_43 assump_44 =>
          cases assump_43
          case inl assump_45 =>
            apply Or.inl
            apply And.intro
            apply Or.inl
            exact assump_45
            apply Or.inl
            exact assump_11
          case inr assump_46 =>
            apply Or.inr
            apply And.intro
            intro assump_55
            exact assump_11
            intro assump_58
            have assump_97 : p0 := by
              exact assump_46
            let assump_62 := assump_44 assump_97
            apply False.elim assump_62
    case inr assump_9 =>
      cases assump_9
      case intro assump_66 assump_67 =>
        cases assump_7
        case intro assump_72 assump_73 =>
          cases assump_72
          case inl assump_74 =>
            apply Or.inl
            apply And.intro
            apply Or.inl
            exact assump_74
            apply Or.inl
            exact assump_67
          case inr assump_75 =>
            apply Or.inr
            apply And.intro
            intro assump_84
            exact assump_67
            intro assump_87
            have assump_98 : p0 := by
              exact assump_75
            let assump_91 := assump_73 assump_98
            apply False.elim assump_91


variable (p6 p1 p0 p3 p2 p5 p4 p7 : Prop)
theorem file25_110727 : ((((((p4 ∧ False) ∨ (True ∨ p2)) → ((False ∧ True) → (False ∨ p6))) ∧ (((p7 → p1) ∨ (False ∨ p7)) → ((p2 ∨ False) → (False ∧ True)))) ∧ ((((p0 → p6) ∨ (p0 → p3)) ∨ ((p7 ∨ p0) → False)) ∧ (((p3 ∧ p5) → False) ∧ ((p1 → p1) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          cases assump_12
          case inl assump_14 =>
            cases assump_11
            case intro assump_18 assump_19 =>
              have assump_61 : (p1 → p1) := by
                intro assump_25
                exact assump_25
              let assump_24 := assump_19 assump_61
              apply False.elim assump_24
          case inr assump_15 =>
            cases assump_11
            case intro assump_33 assump_34 =>
              have assump_62 : (p1 → p1) := by
                intro assump_40
                exact assump_40
              let assump_39 := assump_34 assump_62
              apply False.elim assump_39
        case inr assump_13 =>
          cases assump_11
          case intro assump_48 assump_49 =>
            have assump_63 : (p1 → p1) := by
              intro assump_55
              exact assump_55
            let assump_54 := assump_49 assump_63
            apply False.elim assump_54


variable (p5 p6 p1 p4 p0 p2 p7 : Prop)
theorem file25_112213 : ((((((False ∧ p0) ∨ (False ∨ p6)) → ((p5 → p1) → (p7 → True))) ∨ (((p7 ∧ False) → (p5 ∨ p2)) ∨ ((p6 ∨ p0) → (p1 → p4)))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((False ∧ p0) ∨ (False ∨ p6)) → ((p5 → p1) → (p7 → True))) ∨ (((p7 ∧ False) → (p5 ∨ p2)) ∨ ((p6 ∨ p0) → (p1 → p4)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p5 p7 p2 p3 p4 p1 p0 p6 : Prop)
theorem file25_112745 : (((((p6 → False) ∧ (p1 → False)) → ((p3 → p3) → False)) → (((p7 → False) ∧ (p2 → False)) → False)) → ((((p0 → False) → False) → False) → (((p6 ∧ p7) → (p4 ∨ True)) ∨ ((False → False) ∧ (True ∧ p5))))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    apply Or.inr
    apply True.intro


variable (p7 p0 p6 p1 p4 p5 p2 : Prop)
theorem file25_113170 : (((((p6 → p1) ∧ (False ∧ p0)) ∧ ((p5 ∧ True) ∧ (p4 ∧ p0))) → False) ∨ ((((p2 → False) ∨ (True ∧ p2)) → ((False → False) → False)) ∨ (((p6 → True) → False) ∨ ((p5 ∧ False) ∧ (p7 → False))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        apply False.elim assump_8


variable (p0 p3 p6 p5 p2 p4 : Prop)
theorem file25_113657 : (((((p4 → p3) ∧ (p4 → p3)) ∧ ((p0 → False) ∧ (True → False))) → False) ∨ ((((p2 → p0) → (True → p6)) ∨ ((p5 → p2) → False)) → (((False ∧ p4) → (p6 → False)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        have assump_20 : True := by
          apply True.intro
        let assump_16 := assump_11 assump_20
        apply False.elim assump_16


variable (p7 p4 p1 : Prop)
theorem file25_114224 : (((((p4 ∧ p4) ∨ (p7 ∨ p1)) → ((True → False) → False)) → False) → False) := by
  intro assump_1
  have assump_42 : (((p4 ∧ p4) ∨ (p7 ∨ p1)) → ((True → False) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case inl assump_9 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        have assump_43 : True := by
          apply True.intro
        let assump_19 := assump_6 assump_43
        apply False.elim assump_19
    case inr assump_10 =>
      cases assump_10
      case inl assump_23 =>
        have assump_44 : True := by
          apply True.intro
        let assump_28 := assump_6 assump_44
        apply False.elim assump_28
      case inr assump_24 =>
        have assump_45 : True := by
          apply True.intro
        let assump_35 := assump_6 assump_45
        apply False.elim assump_35
  let assump_4 := assump_1 assump_42
  apply False.elim assump_4


variable (p1 p0 p3 p7 p2 p6 p5 : Prop)
theorem file25_115199 : (((((p2 ∧ False) → (False ∧ p5)) ∧ ((p6 ∨ p7) → (p5 → False))) ∧ (((p7 ∧ p7) ∧ (True → False)) → ((p3 → p6) ∧ (p3 → False)))) → ((((p3 ∧ p2) ∧ (p5 ∨ True)) ∨ ((True → False) → (p6 ∧ p1))) ∧ (((p2 → p3) → (p7 ∨ p1)) → ((True ∨ p6) ∨ (True ∨ p0))))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply Or.inr
      intro assump_12
      apply And.intro
      have assump_38 : True := by
        apply True.intro
      let assump_15 := assump_12 assump_38
      apply False.elim assump_15
      have assump_39 : True := by
        apply True.intro
      let assump_21 := assump_12 assump_39
      apply False.elim assump_21
  intro assump_25
  cases assump_1
  case intro assump_28 assump_29 =>
    cases assump_28
    case intro assump_30 assump_31 =>
      apply Or.inl
      apply Or.inl
      apply True.intro


variable (p7 p6 p4 p0 p5 p2 p1 : Prop)
theorem file25_116180 : (((((True ∧ p4) ∧ (p4 → p2)) ∧ ((False ∨ False) ∨ (p0 → p2))) → (((p0 ∧ False) → False) → ((p1 → p1) ∧ (p7 → True)))) ∨ ((((p7 → False) ∧ (True → False)) → False) → (((p5 ∧ p7) → False) ∧ ((p2 → p6) → False)))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  cases assump_1
  case intro assump_8 assump_9 =>
    cases assump_8
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_9
        case inl assump_20 =>
          cases assump_20
          case inl assump_22 =>
            apply False.elim assump_22
          case inr assump_23 =>
            apply False.elim assump_23
        case inr assump_21 =>
          exact assump_3
  intro assump_30
  apply True.intro


variable (p3 p7 p6 p1 p5 p2 p0 : Prop)
theorem file25_117027 : (((((p2 ∨ True) → False) → ((p7 ∧ False) → False)) → False) → ((((p3 ∨ p0) ∨ (p5 → p0)) ∨ ((p6 → False) ∨ (True ∨ p7))) ∧ (((p1 → False) → False) → False))) := by
  intro assump_1
  apply And.intro
  apply Or.inl
  apply Or.inr
  intro assump_4
  have assump_37 : (((p2 ∨ True) → False) → ((p7 ∧ False) → False)) := by
    intro assump_9
    intro assump_10
    cases assump_10
    case intro assump_11 assump_12 =>
      apply False.elim assump_12
  let assump_8 := assump_1 assump_37
  apply False.elim assump_8
  intro assump_20
  have assump_38 : (((p2 ∨ True) → False) → ((p7 ∧ False) → False)) := by
    intro assump_26
    intro assump_27
    cases assump_27
    case intro assump_28 assump_29 =>
      apply False.elim assump_29
  let assump_25 := assump_1 assump_38
  apply False.elim assump_25


variable (p7 p4 p1 p2 p6 : Prop)
theorem file25_117888 : ((((((p6 → False) ∨ (p2 → False)) ∨ ((p7 ∨ True) → False)) → (((p7 ∨ p1) ∨ (p7 ∨ p1)) → ((p1 ∨ True) ∨ (p4 ∧ p7)))) → False) → False) := by
  intro assump_1
  have assump_64 : ((((p6 → False) ∨ (p2 → False)) ∨ ((p7 ∨ True) → False)) → (((p7 ∨ p1) ∨ (p7 ∨ p1)) → ((p1 ∨ True) ∨ (p4 ∧ p7)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_5
        case inl assump_13 =>
          cases assump_13
          case inl assump_15 =>
            apply Or.inl
            apply Or.inr
            apply True.intro
          case inr assump_16 =>
            apply Or.inl
            apply Or.inr
            apply True.intro
        case inr assump_14 =>
          apply Or.inl
          apply Or.inr
          apply True.intro
      case inr assump_10 =>
        cases assump_5
        case inl assump_25 =>
          cases assump_25
          case inl assump_27 =>
            apply Or.inl
            apply Or.inl
            exact assump_10
          case inr assump_28 =>
            apply Or.inl
            apply Or.inl
            exact assump_10
        case inr assump_26 =>
          apply Or.inl
          apply Or.inl
          exact assump_10
    case inr assump_8 =>
      cases assump_8
      case inl assump_35 =>
        cases assump_5
        case inl assump_39 =>
          cases assump_39
          case inl assump_41 =>
            apply Or.inl
            apply Or.inr
            apply True.intro
          case inr assump_42 =>
            apply Or.inl
            apply Or.inr
            apply True.intro
        case inr assump_40 =>
          apply Or.inl
          apply Or.inr
          apply True.intro
      case inr assump_36 =>
        cases assump_5
        case inl assump_51 =>
          cases assump_51
          case inl assump_53 =>
            apply Or.inl
            apply Or.inl
            exact assump_36
          case inr assump_54 =>
            apply Or.inl
            apply Or.inl
            exact assump_36
        case inr assump_52 =>
          apply Or.inl
          apply Or.inl
          exact assump_36
  let assump_4 := assump_1 assump_64
  apply False.elim assump_4


variable (p7 p5 p6 p2 : Prop)
theorem file25_120173 : ((((((p6 ∧ True) → (p5 ∧ p2)) ∧ ((True ∨ p7) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p6 ∧ True) → (p5 ∧ p2)) ∧ ((True ∨ p7) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_20 : (True ∨ p7) := by
        apply Or.inl
        apply True.intro
      let assump_12 := assump_7 assump_20
      apply False.elim assump_12
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p5 p4 p3 p6 p2 : Prop)
theorem file25_120723 : ((((((p5 ∧ p5) → False) ∨ ((p4 ∨ False) → (p3 ∨ True))) → (((p2 → p6) ∧ (p3 ∨ p3)) ∨ ((p3 → False) ∧ (p3 ∧ p6)))) ∧ ((((False → False) ∨ (p3 → False)) ∨ ((p4 ∧ False) → False)) ∧ (((p2 ∧ p4) → (p2 ∧ True)) → False))) → False) := by
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    cases assump_11
    case intro assump_14 assump_15 =>
      cases assump_14
      case inl assump_16 =>
        cases assump_16
        case inl assump_18 =>
          have assump_65 : ((p2 ∧ p4) → (p2 ∧ True)) := by
            intro assump_25
            apply And.intro
            cases assump_25
            case intro assump_26 assump_27 =>
              exact assump_26
            apply True.intro
          let assump_24 := assump_15 assump_65
          apply False.elim assump_24
        case inr assump_19 =>
          have assump_66 : ((p2 ∧ p4) → (p2 ∧ True)) := by
            intro assump_40
            apply And.intro
            cases assump_40
            case intro assump_41 assump_42 =>
              exact assump_41
            apply True.intro
          let assump_39 := assump_15 assump_66
          apply False.elim assump_39
      case inr assump_17 =>
        have assump_67 : ((p2 ∧ p4) → (p2 ∧ True)) := by
          intro assump_55
          apply And.intro
          cases assump_55
          case intro assump_56 assump_57 =>
            exact assump_56
          apply True.intro
        let assump_54 := assump_15 assump_67
        apply False.elim assump_54


variable (p3 p4 p6 p5 p1 : Prop)
theorem file25_122280 : (((((p4 ∧ False) ∧ (p3 ∨ p3)) → False) → False) → ((((True ∨ p1) ∨ (p5 → False)) → ((p5 ∧ p3) ∧ (p6 → False))) → False)) := by
  intro assump_5
  intro assump_6
  have assump_24 : (((p4 ∧ False) ∧ (p3 ∨ p3)) → False) := by
    intro assump_12
    cases assump_12
    case intro assump_13 assump_14 =>
      cases assump_13
      case intro assump_15 assump_16 =>
        apply False.elim assump_16
  let assump_11 := assump_5 assump_24
  apply False.elim assump_11


variable (p0 p4 p1 p6 p2 : Prop)
theorem file25_122802 : ((((((p1 → p6) → (True ∨ p2)) → False) → (((False → False) ∧ (True → False)) ∧ ((p6 → False) ∧ (p0 ∧ p4)))) → False) → False) := by
  intro assump_9
  have assump_62 : ((((p1 → p6) → (True ∨ p2)) → False) → (((False → False) ∧ (True → False)) ∧ ((p6 → False) ∧ (p0 ∧ p4)))) := by
    intro assump_13
    apply And.intro
    apply And.intro
    intro assump_14
    apply False.elim assump_14
    intro assump_17
    have assump_63 : ((p1 → p6) → (True ∨ p2)) := by
      intro assump_23
      apply Or.inl
      apply True.intro
    let assump_22 := assump_13 assump_63
    apply False.elim assump_22
    apply And.intro
    intro assump_29
    have assump_64 : ((p1 → p6) → (True ∨ p2)) := by
      intro assump_35
      apply Or.inl
      apply True.intro
    let assump_34 := assump_13 assump_64
    apply False.elim assump_34
    apply And.intro
    have assump_65 : ((p1 → p6) → (True ∨ p2)) := by
      intro assump_44
      apply Or.inl
      apply True.intro
    let assump_43 := assump_13 assump_65
    apply False.elim assump_43
    have assump_66 : ((p1 → p6) → (True ∨ p2)) := by
      intro assump_53
      apply Or.inl
      apply True.intro
    let assump_52 := assump_13 assump_66
    apply False.elim assump_52
  let assump_12 := assump_9 assump_62
  apply False.elim assump_12


variable (p6 p0 p2 p1 p4 p7 p3 : Prop)
theorem file25_124159 : (((((p1 ∨ True) → False) ∧ ((p7 → True) → False)) ∧ (((p6 ∨ p3) ∧ (p0 ∧ p7)) → False)) → ((((False ∧ p7) → False) → False) ∧ (((p4 → False) ∧ (p7 ∧ True)) ∨ ((p2 → False) ∨ (p4 ∧ True))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      have assump_51 : (p7 → True) := by
        intro assump_17
        apply True.intro
      let assump_16 := assump_8 assump_51
      apply False.elim assump_16
  cases assump_1
  case intro assump_21 assump_22 =>
    cases assump_21
    case intro assump_23 assump_24 =>
      apply Or.inr
      apply Or.inl
      intro assump_41
      have assump_52 : (p7 → True) := by
        intro assump_47
        apply True.intro
      let assump_46 := assump_24 assump_52
      apply False.elim assump_46


variable (p7 p3 p1 p4 p5 : Prop)
theorem file25_125071 : (((((p7 ∨ p1) → False) → False) → False) → ((((p5 → False) ∧ (p7 ∧ p4)) ∨ ((p3 ∨ p3) ∧ (p3 ∧ p1))) → (((p4 ∧ p7) → (p5 ∨ p3)) ∨ ((True ∧ True) ∨ (p3 ∧ True))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_6
      case intro assump_9 assump_10 =>
        apply Or.inl
        intro assump_17
        cases assump_17
        case intro assump_18 assump_19 =>
          have assump_75 : (((p7 ∨ p1) → False) → False) := by
            intro assump_27
            have assump_76 : (p7 ∨ p1) := by
              apply Or.inl
              exact assump_19
            let assump_30 := assump_27 assump_76
            apply False.elim assump_30
          let assump_26 := assump_1 assump_75
          apply False.elim assump_26
  case inr assump_4 =>
    cases assump_4
    case intro assump_37 assump_38 =>
      cases assump_37
      case inl assump_39 =>
        cases assump_38
        case intro assump_43 assump_44 =>
          apply Or.inl
          intro assump_51
          cases assump_51
          case intro assump_52 assump_53 =>
            apply Or.inr
            exact assump_43
      case inr assump_40 =>
        cases assump_38
        case intro assump_60 assump_61 =>
          apply Or.inl
          intro assump_68
          cases assump_68
          case intro assump_69 assump_70 =>
            apply Or.inr
            exact assump_60


variable (p4 p2 p3 p1 p7 : Prop)
theorem file25_126593 : (((((p3 ∧ False) ∨ (p7 → True)) → False) → False) ∨ ((((p1 → p4) ∧ (p2 ∧ p1)) → False) ∨ (((False ∧ p4) ∨ (p2 ∨ p3)) → ((p7 → False) ∧ (p7 ∨ p2))))) := by
  apply Or.inl
  intro assump_1
  have assump_9 : ((p3 ∧ False) ∨ (p7 → True)) := by
    apply Or.inr
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_9
  apply False.elim assump_4


variable (p4 p6 p1 p7 p5 p0 p3 p2 : Prop)
theorem file25_127020 : ((((((p2 ∧ True) ∨ (p4 ∨ p1)) → False) → (((p7 ∨ p3) ∧ (p0 → False)) ∨ ((p1 → False) ∨ (p6 ∧ False)))) ∧ ((((p5 → False) ∧ (True → False)) → ((p4 ∧ p1) → (p3 ∨ p5))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_30 : (((p5 → False) ∧ (True → False)) → ((p4 ∧ p1) → (p3 ∨ p5))) := by
      intro assump_9
      intro assump_10
      cases assump_10
      case intro assump_11 assump_12 =>
        cases assump_9
        case intro assump_17 assump_18 =>
          have assump_31 : True := by
            apply True.intro
          let assump_23 := assump_18 assump_31
          apply False.elim assump_23
    let assump_8 := assump_3 assump_30
    apply False.elim assump_8


variable (p7 p5 p6 p4 p1 p3 : Prop)
theorem file25_127816 : ((((((p3 ∧ p3) ∧ (p5 ∧ p4)) ∨ ((p1 ∧ p5) ∨ (False ∨ p4))) ∨ (((p5 → False) → (False → False)) ∨ ((p7 ∧ p6) → False))) → False) → False) := by
  intro assump_1
  have assump_12 : ((((p3 ∧ p3) ∧ (p5 ∧ p4)) ∨ ((p1 ∧ p5) ∨ (False ∨ p4))) ∨ (((p5 → False) → (False → False)) ∨ ((p7 ∧ p6) → False))) := by
    apply Or.inr
    apply Or.inl
    intro assump_5
    intro assump_6
    apply False.elim assump_6
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p0 p4 p3 p5 : Prop)
theorem file25_128337 : ((((((False ∧ False) ∧ (p0 → False)) → ((p4 → False) ∧ (p5 ∨ p3))) → (((False → False) → False) → ((p0 → p4) → False))) → False) → False) := by
  intro assump_1
  have assump_25 : ((((False ∧ False) ∧ (p0 → False)) → ((p4 → False) ∧ (p5 ∨ p3))) → (((False → False) → False) → ((p0 → p4) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    have assump_26 : (False → False) := by
      intro assump_16
      apply False.elim assump_16
    let assump_15 := assump_6 assump_26
    apply False.elim assump_15
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p1 p3 p4 p7 p6 p0 p5 : Prop)
theorem file25_128995 : (((((p0 → p4) → False) ∧ ((p6 ∧ True) ∧ (p0 → False))) → (((p3 ∧ p5) → False) ∧ ((p5 → False) ∧ (p1 → False)))) ∨ ((((p1 ∧ p7) ∨ (p4 ∨ False)) → ((p3 → False) ∧ (True → p7))) ∧ (((True → False) → (p0 ∨ p4)) ∨ ((p6 ∨ p4) → False)))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_1
    case intro assump_9 assump_10 =>
      cases assump_10
      case intro assump_13 assump_14 =>
        cases assump_13
        case intro assump_15 assump_16 =>
          have assump_99 : (p0 → p4) := by
            intro assump_26
            have assump_100 : p0 := by
              exact assump_26
            let assump_30 := assump_14 assump_100
            apply False.elim assump_30
          let assump_25 := assump_9 assump_99
          apply False.elim assump_25
  apply And.intro
  intro assump_37
  cases assump_1
  case intro assump_40 assump_41 =>
    cases assump_41
    case intro assump_44 assump_45 =>
      cases assump_44
      case intro assump_46 assump_47 =>
        have assump_101 : (p0 → p4) := by
          intro assump_57
          have assump_102 : p0 := by
            exact assump_57
          let assump_61 := assump_45 assump_102
          apply False.elim assump_61
        let assump_56 := assump_40 assump_101
        apply False.elim assump_56
  intro assump_68
  cases assump_1
  case intro assump_71 assump_72 =>
    cases assump_72
    case intro assump_75 assump_76 =>
      cases assump_75
      case intro assump_77 assump_78 =>
        have assump_103 : (p0 → p4) := by
          intro assump_88
          have assump_104 : p0 := by
            exact assump_88
          let assump_92 := assump_76 assump_104
          apply False.elim assump_92
        let assump_87 := assump_71 assump_103
        apply False.elim assump_87


variable (p4 p5 p7 p0 p1 : Prop)
theorem file25_130902 : ((((((p7 ∧ p4) → (p1 ∨ p4)) → False) → (((p1 → False) → (True → False)) → ((p0 → False) ∧ (p5 → p1)))) → False) → False) := by
  intro assump_1
  have assump_46 : ((((p7 ∧ p4) → (p1 ∨ p4)) → False) → (((p1 → False) → (True → False)) → ((p0 → False) ∧ (p5 → p1)))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    intro assump_7
    have assump_47 : ((p7 ∧ p4) → (p1 ∨ p4)) := by
      intro assump_15
      cases assump_15
      case intro assump_16 assump_17 =>
        apply Or.inr
        exact assump_17
    let assump_14 := assump_5 assump_47
    apply False.elim assump_14
    intro assump_25
    have assump_48 : ((p7 ∧ p4) → (p1 ∨ p4)) := by
      intro assump_33
      cases assump_33
      case intro assump_34 assump_35 =>
        apply Or.inr
        exact assump_35
    let assump_32 := assump_5 assump_48
    apply False.elim assump_32
  let assump_4 := assump_1 assump_46
  apply False.elim assump_4


variable (p1 p0 p5 p2 p7 p6 p3 : Prop)
theorem file25_131899 : (((((p2 → p7) ∨ (p2 ∨ True)) ∧ ((p7 ∧ p7) → (False → p0))) → False) → ((((True ∧ True) ∨ (p1 → False)) ∨ ((p6 ∧ p3) → (p3 → True))) ∨ (((p6 → p5) ∨ (p2 ∧ True)) ∨ ((p7 → p5) ∧ (p1 → False))))) := by
  intro assump_16
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply And.intro
  apply True.intro
  apply True.intro


variable (p1 p5 p4 p7 p2 : Prop)
theorem file25_132274 : ((((((p1 ∨ True) ∨ (p4 → p1)) → False) → (((p5 → False) → False) → ((p2 ∨ p5) ∨ (p7 → False)))) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p1 ∨ True) ∨ (p4 → p1)) → False) → (((p5 → False) → False) → ((p2 ∨ p5) ∨ (p7 → False)))) := by
    intro assump_5
    intro assump_6
    apply Or.inr
    intro assump_11
    have assump_23 : ((p1 ∨ True) ∨ (p4 → p1)) := by
      apply Or.inl
      apply Or.inr
      apply True.intro
    let assump_15 := assump_5 assump_23
    apply False.elim assump_15
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p7 p6 p3 p2 p4 p5 p1 : Prop)
theorem file25_132918 : ((((((p3 → False) → False) → ((p2 → False) → False)) ∧ (((p2 ∧ p5) → False) ∨ ((p6 ∧ p2) → (p3 ∧ p4)))) ∧ ((((True → True) → (p1 ∧ False)) ∧ ((p4 ∧ p1) ∧ (False → False))) ∧ (((False ∧ False) ∨ (p6 → p7)) ∨ ((p5 ∧ p6) ∨ (p5 ∧ p7))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        cases assump_3
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_15
            case intro assump_18 assump_19 =>
              cases assump_18
              case intro assump_20 assump_21 =>
                cases assump_13
                case inl assump_28 =>
                  cases assump_28
                  case inl assump_30 =>
                    cases assump_30
                    case intro assump_32 assump_33 =>
                      apply False.elim assump_32
                  case inr assump_31 =>
                    have assump_164 : (True → True) := by
                      intro assump_43
                      apply True.intro
                    let assump_42 := assump_14 assump_164
                    let assump_44 := And.right assump_42
                    apply False.elim assump_44
                case inr assump_29 =>
                  cases assump_29
                  case inl assump_49 =>
                    cases assump_49
                    case intro assump_51 assump_52 =>
                      have assump_165 : (True → True) := by
                        intro assump_63
                        apply True.intro
                      let assump_62 := assump_14 assump_165
                      let assump_64 := And.right assump_62
                      apply False.elim assump_64
                  case inr assump_50 =>
                    cases assump_50
                    case intro assump_69 assump_70 =>
                      have assump_166 : (True → True) := by
                        intro assump_81
                        apply True.intro
                      let assump_80 := assump_14 assump_166
                      let assump_82 := And.right assump_80
                      apply False.elim assump_82
      case inr assump_9 =>
        cases assump_3
        case intro assump_89 assump_90 =>
          cases assump_89
          case intro assump_91 assump_92 =>
            cases assump_92
            case intro assump_95 assump_96 =>
              cases assump_95
              case intro assump_97 assump_98 =>
                cases assump_90
                case inl assump_105 =>
                  cases assump_105
                  case inl assump_107 =>
                    cases assump_107
                    case intro assump_109 assump_110 =>
                      apply False.elim assump_109
                  case inr assump_108 =>
                    have assump_167 : (True → True) := by
                      intro assump_120
                      apply True.intro
                    let assump_119 := assump_91 assump_167
                    let assump_121 := And.right assump_119
                    apply False.elim assump_121
                case inr assump_106 =>
                  cases assump_106
                  case inl assump_126 =>
                    cases assump_126
                    case intro assump_128 assump_129 =>
                      have assump_168 : (True → True) := by
                        intro assump_140
                        apply True.intro
                      let assump_139 := assump_91 assump_168
                      let assump_141 := And.right assump_139
                      apply False.elim assump_141
                  case inr assump_127 =>
                    cases assump_127
                    case intro assump_146 assump_147 =>
                      have assump_169 : (True → True) := by
                        intro assump_158
                        apply True.intro
                      let assump_157 := assump_91 assump_169
                      let assump_159 := And.right assump_157
                      apply False.elim assump_159


