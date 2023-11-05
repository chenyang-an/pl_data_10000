variable (p5 p2 p6 p1 p4 : Prop)
theorem file82_41 : (((((p2 → p2) ∨ (p1 → True)) → False) → False) ∧ ((((p1 ∨ p5) ∨ (True → False)) ∨ ((True → False) → False)) → (((True ∧ True) ∧ (p2 ∨ p4)) → ((p2 ∧ False) → (p6 ∧ p5))))) := by
  apply And.intro
  intro assump_1
  have assump_26 : ((p2 → p2) ∨ (p1 → True)) := by
    apply Or.inl
    intro assump_5
    exact assump_5
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4
  intro assump_11
  intro assump_12
  intro assump_13
  apply And.intro
  cases assump_13
  case intro assump_14 assump_15 =>
    apply False.elim assump_15
  cases assump_13
  case intro assump_20 assump_21 =>
    apply False.elim assump_21


variable (p1 p6 p7 p2 p4 : Prop)
theorem file82_723 : (((((p7 → False) → (p7 → False)) → False) → False) ∨ ((((p7 ∧ p1) → (p2 ∨ p4)) ∧ ((p6 → p6) ∨ (p2 → False))) → False)) := by
  apply Or.inl
  intro assump_1
  have assump_18 : ((p7 → False) → (p7 → False)) := by
    intro assump_5
    intro assump_6
    have assump_19 : p7 := by
      exact assump_6
    let assump_11 := assump_5 assump_19
    apply False.elim assump_11
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p6 p3 p5 p7 p1 : Prop)
theorem file82_1217 : ((((((p1 → p1) → (p1 → False)) → False) ∨ (((p5 ∨ p6) → False) → ((False → p6) ∨ (True → p7)))) ∧ ((((p6 → False) → (False → False)) ∨ ((p3 → False) → False)) → False)) → False) := by
  intro assump_26
  cases assump_26
  case intro assump_27 assump_28 =>
    cases assump_27
    case inl assump_29 =>
      have assump_55 : (((p6 → False) → (False → False)) ∨ ((p3 → False) → False)) := by
        apply Or.inl
        intro assump_36
        intro assump_37
        apply False.elim assump_37
      let assump_35 := assump_28 assump_55
      apply False.elim assump_35
    case inr assump_30 =>
      have assump_56 : (((p6 → False) → (False → False)) ∨ ((p3 → False) → False)) := by
        apply Or.inl
        intro assump_48
        intro assump_49
        apply False.elim assump_49
      let assump_47 := assump_28 assump_56
      apply False.elim assump_47


variable (p6 p0 p3 p1 : Prop)
theorem file82_2137 : ((((((p1 ∧ p1) → (False → False)) ∧ ((p1 ∧ False) → (p0 → False))) ∧ (((p0 ∨ p3) → (p0 ∨ p3)) → ((True → False) → (p6 → False)))) → False) → False) := by
  intro assump_1
  have assump_36 : ((((p1 ∧ p1) → (False → False)) ∧ ((p1 ∧ False) → (p0 → False))) ∧ (((p0 ∨ p3) → (p0 ∨ p3)) → ((True → False) → (p6 → False)))) := by
    apply And.intro
    apply And.intro
    intro assump_5
    intro assump_6
    apply False.elim assump_6
    intro assump_9
    intro assump_10
    cases assump_9
    case intro assump_13 assump_14 =>
      apply False.elim assump_14
    intro assump_19
    intro assump_20
    intro assump_21
    have assump_37 : True := by
      apply True.intro
    let assump_29 := assump_20 assump_37
    apply False.elim assump_29
  let assump_4 := assump_1 assump_36
  apply False.elim assump_4


variable (p3 p6 p4 p0 p2 p1 p7 p5 : Prop)
theorem file82_3016 : (((((False ∧ p4) ∧ (True → p3)) ∨ ((True ∨ p1) ∧ (p3 ∨ p1))) ∨ (((p6 → p5) ∧ (p6 → p0)) → False)) → ((((p4 → p6) → (True → True)) ∧ ((False → False) → (p1 → p1))) ∧ (((p6 ∧ True) ∧ (p6 ∧ p3)) → ((p2 ∧ p3) → (p7 ∨ True))))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  intro assump_3
  apply True.intro
  intro assump_4
  intro assump_5
  cases assump_1
  case inl assump_10 =>
    cases assump_10
    case inl assump_12 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          apply False.elim assump_16
    case inr assump_13 =>
      cases assump_13
      case intro assump_20 assump_21 =>
        cases assump_20
        case inl assump_22 =>
          cases assump_21
          case inl assump_26 =>
            exact assump_5
          case inr assump_27 =>
            exact assump_27
        case inr assump_23 =>
          cases assump_21
          case inl assump_34 =>
            exact assump_23
          case inr assump_35 =>
            exact assump_35
  case inr assump_11 =>
    exact assump_5
  intro assump_42
  intro assump_43
  cases assump_43
  case intro assump_44 assump_45 =>
    cases assump_42
    case intro assump_50 assump_51 =>
      cases assump_50
      case intro assump_52 assump_53 =>
        cases assump_51
        case intro assump_58 assump_59 =>
          cases assump_1
          case inl assump_64 =>
            cases assump_64
            case inl assump_66 =>
              cases assump_66
              case intro assump_68 assump_69 =>
                cases assump_68
                case intro assump_70 assump_71 =>
                  apply False.elim assump_70
            case inr assump_67 =>
              cases assump_67
              case intro assump_74 assump_75 =>
                cases assump_74
                case inl assump_76 =>
                  cases assump_75
                  case inl assump_80 =>
                    apply Or.inr
                    apply True.intro
                  case inr assump_81 =>
                    apply Or.inr
                    apply True.intro
                case inr assump_77 =>
                  cases assump_75
                  case inl assump_88 =>
                    apply Or.inr
                    apply True.intro
                  case inr assump_89 =>
                    apply Or.inr
                    apply True.intro
          case inr assump_65 =>
            apply Or.inr
            apply True.intro


variable (p0 p5 p6 p1 p2 p7 p3 p4 : Prop)
theorem file82_5623 : (((((p3 → p5) ∧ (p0 ∧ False)) → False) ∧ (((p6 ∨ p4) ∨ (p2 → True)) ∨ ((p7 → False) ∨ (True → p7)))) ∨ ((((p3 → p2) ∧ (p0 → p4)) ∨ ((p0 ∨ p1) ∨ (True ∧ True))) → False)) := by
  apply Or.inl
  apply And.intro
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      apply False.elim assump_7
  apply Or.inl
  apply Or.inr
  intro assump_12
  apply True.intro


variable (p6 p5 : Prop)
theorem file82_6102 : ((((((False → p5) → (True ∨ p6)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_18 : ((((False → p5) → (True ∨ p6)) → False) → False) := by
    intro assump_5
    have assump_19 : ((False → p5) → (True ∨ p6)) := by
      intro assump_9
      apply Or.inl
      apply True.intro
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p1 p7 p4 p2 p3 p0 p5 : Prop)
theorem file82_6603 : ((((((p1 → p0) → (p7 → p2)) → False) → False) ∧ ((((p5 → False) ∨ (p0 ∧ p1)) ∨ ((p1 ∨ p4) ∧ (p2 → p3))) ∧ (((p4 → True) → False) ∧ ((p3 → False) ∧ (p4 → p0))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_7
          case intro assump_14 assump_15 =>
            cases assump_15
            case intro assump_18 assump_19 =>
              have assump_101 : (p4 → True) := by
                intro assump_27
                apply True.intro
              let assump_26 := assump_14 assump_101
              apply False.elim assump_26
        case inr assump_11 =>
          cases assump_11
          case intro assump_31 assump_32 =>
            cases assump_7
            case intro assump_37 assump_38 =>
              cases assump_38
              case intro assump_41 assump_42 =>
                have assump_102 : (p4 → True) := by
                  intro assump_50
                  apply True.intro
                let assump_49 := assump_37 assump_102
                apply False.elim assump_49
      case inr assump_9 =>
        cases assump_9
        case intro assump_54 assump_55 =>
          cases assump_54
          case inl assump_56 =>
            cases assump_7
            case intro assump_62 assump_63 =>
              cases assump_63
              case intro assump_66 assump_67 =>
                have assump_103 : (p4 → True) := by
                  intro assump_75
                  apply True.intro
                let assump_74 := assump_62 assump_103
                apply False.elim assump_74
          case inr assump_57 =>
            cases assump_7
            case intro assump_83 assump_84 =>
              cases assump_84
              case intro assump_87 assump_88 =>
                have assump_104 : (p4 → True) := by
                  intro assump_97
                  apply True.intro
                let assump_96 := assump_83 assump_104
                apply False.elim assump_96


variable (p7 p2 p3 p0 p6 p4 p5 : Prop)
theorem file82_8806 : (((((p5 → p4) → False) → ((True ∧ False) → (True → False))) ∧ (((p6 → False) ∧ (p7 ∧ False)) → ((p5 → p4) ∧ (p2 ∨ p3)))) ∨ ((((p0 ∧ False) → (True ∨ p0)) ∧ ((p4 → p0) → False)) ∧ (((p0 ∧ p7) → False) → False))) := by
  apply Or.inl
  apply And.intro
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    apply False.elim assump_7
  intro assump_12
  apply And.intro
  intro assump_13
  cases assump_12
  case intro assump_16 assump_17 =>
    cases assump_17
    case intro assump_20 assump_21 =>
      apply False.elim assump_21
  cases assump_12
  case intro assump_26 assump_27 =>
    cases assump_27
    case intro assump_30 assump_31 =>
      apply False.elim assump_31


variable (p0 p3 p7 p6 p1 p5 : Prop)
theorem file82_9592 : (((((p0 → False) ∧ (p5 ∨ p3)) → ((p7 → True) ∧ (False → False))) → (((p3 ∨ p3) ∨ (p1 ∨ True)) ∨ ((p3 → False) ∨ (p6 ∧ p7)))) → ((((False ∧ p5) → (p5 → False)) ∨ ((p6 ∧ p3) → False)) ∨ (((p7 ∧ p6) → False) → False))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_4
  case intro assump_8 assump_9 =>
    apply False.elim assump_8


variable (p4 p6 p7 p5 p0 p2 : Prop)
theorem file82_10036 : ((((((p2 ∧ False) → False) ∨ ((p6 ∨ p4) → False)) ∧ (((p7 → True) ∨ (True → p5)) ∨ ((p0 → p5) ∧ (p2 ∨ p5)))) → False) → False) := by
  intro assump_1
  have assump_16 : ((((p2 ∧ False) → False) ∨ ((p6 ∨ p4) → False)) ∧ (((p7 → True) ∨ (True → p5)) ∨ ((p0 → p5) ∧ (p2 ∨ p5)))) := by
    apply And.intro
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_7
    apply Or.inl
    apply Or.inl
    intro assump_12
    apply True.intro
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p4 p3 p5 p6 p2 p1 p7 : Prop)
theorem file82_10664 : (((((True ∨ p2) → False) → ((p1 ∨ False) → (p1 → p7))) ∨ (((p1 → False) ∧ (p6 ∨ p2)) ∨ ((p6 → True) ∧ (p5 ∧ p4)))) → ((((False ∧ p7) → (False → False)) ∨ ((p1 → False) ∨ (p4 → p5))) ∨ (((p3 → False) → (True ∧ p2)) ∨ ((p2 → True) ∨ (p1 → False))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply Or.inl
    intro assump_6
    intro assump_7
    apply False.elim assump_7
  case inr assump_3 =>
    cases assump_3
    case inl assump_10 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_13
        case inl assump_16 =>
          apply Or.inl
          apply Or.inl
          intro assump_20
          intro assump_21
          apply False.elim assump_21
        case inr assump_17 =>
          apply Or.inl
          apply Or.inl
          intro assump_26
          intro assump_27
          apply False.elim assump_27
    case inr assump_11 =>
      cases assump_11
      case intro assump_30 assump_31 =>
        cases assump_31
        case intro assump_34 assump_35 =>
          apply Or.inl
          apply Or.inl
          intro assump_40
          intro assump_41
          apply False.elim assump_41


variable (p3 p0 p4 p5 p7 p1 p2 : Prop)
theorem file82_11913 : (((((p3 → False) → False) → ((p5 → True) ∨ (p4 → p4))) ∨ (((p7 → False) → False) → False)) ∨ ((((p0 → p1) ∨ (p5 → p5)) ∨ ((p2 → False) → False)) → (((p1 ∧ p1) ∨ (p0 ∧ p5)) ∨ ((False ∨ p5) ∨ (p3 ∧ p0))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  apply True.intro


variable (p0 p1 p5 p3 p7 p2 p6 p4 : Prop)
theorem file82_12287 : ((((((p0 → False) → False) ∧ ((p5 → True) → (p3 → p6))) ∧ (((p0 ∧ p6) → (p2 ∧ p1)) → ((False ∨ p0) → False))) ∧ ((((p3 → p4) ∧ (p3 → p3)) ∧ ((p2 ∧ False) ∧ (True ∧ p5))) ∧ (((p4 → p6) ∧ (p2 ∨ p0)) ∧ ((False ∧ p1) → (p7 ∧ p5))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_3
        case intro assump_14 assump_15 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              cases assump_17
              case intro assump_24 assump_25 =>
                cases assump_24
                case intro assump_26 assump_27 =>
                  apply False.elim assump_27


variable (p2 p1 p0 p7 p6 p5 : Prop)
theorem file82_13187 : ((((((p1 → False) ∧ (p6 ∧ p2)) → ((True ∧ p1) ∨ (p1 → p5))) ∨ (((p0 → False) → False) ∧ ((p0 ∨ p7) ∧ (p5 ∧ p7)))) → False) → False) := by
  intro assump_24
  have assump_52 : ((((p1 → False) ∧ (p6 ∧ p2)) → ((True ∧ p1) ∨ (p1 → p5))) ∨ (((p0 → False) → False) ∧ ((p0 ∨ p7) ∧ (p5 ∧ p7)))) := by
    apply Or.inl
    intro assump_28
    cases assump_28
    case intro assump_29 assump_30 =>
      cases assump_30
      case intro assump_33 assump_34 =>
        apply Or.inr
        intro assump_39
        have assump_53 : p1 := by
          exact assump_39
        let assump_45 := assump_29 assump_53
        apply False.elim assump_45
  let assump_27 := assump_24 assump_52
  apply False.elim assump_27


variable (p7 p2 p4 p1 : Prop)
theorem file82_13944 : (((((False ∧ p7) ∧ (p7 → False)) → ((False ∨ p7) → False)) ∨ (((p2 → False) ∧ (p4 ∧ p1)) → False)) ∨ ((((p1 → False) ∧ (False ∨ False)) ∧ ((p4 → p2) → False)) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    apply False.elim assump_3
  case inr assump_4 =>
    cases assump_1
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        apply False.elim assump_11


variable (p6 p4 p2 p0 p1 p5 p7 p3 : Prop)
theorem file82_14494 : (((((p5 → p5) → (p2 ∧ p6)) → False) → (((p4 ∧ p1) ∧ (p0 ∧ p3)) ∨ ((p3 → False) ∨ (p7 ∨ p1)))) → ((((p6 → p6) → (p4 → p7)) ∧ ((p6 ∧ p3) ∨ (False ∧ False))) → (((True → False) → False) ∨ ((False → p3) → (p6 ∧ p4))))) := by
  intro assump_24
  intro assump_25
  cases assump_25
  case intro assump_26 assump_27 =>
    cases assump_27
    case inl assump_30 =>
      cases assump_30
      case intro assump_32 assump_33 =>
        apply Or.inl
        intro assump_40
        have assump_51 : True := by
          apply True.intro
        let assump_43 := assump_40 assump_51
        apply False.elim assump_43
    case inr assump_31 =>
      cases assump_31
      case intro assump_47 assump_48 =>
        apply False.elim assump_47


variable (p2 p6 p4 p5 p1 p3 : Prop)
theorem file82_15284 : ((((((p6 → False) → (p2 ∨ p1)) ∧ ((p3 → False) ∧ (p2 → p2))) ∧ (((p4 → False) ∨ (True ∧ p5)) → ((p6 → False) → False))) ∧ ((((False ∧ p2) ∧ (p4 → False)) → False) → False)) → False) := by
  intro assump_24
  cases assump_24
  case intro assump_25 assump_26 =>
    cases assump_25
    case intro assump_27 assump_28 =>
      cases assump_27
      case intro assump_29 assump_30 =>
        cases assump_30
        case intro assump_33 assump_34 =>
          have assump_54 : (((False ∧ p2) ∧ (p4 → False)) → False) := by
            intro assump_44
            cases assump_44
            case intro assump_45 assump_46 =>
              cases assump_45
              case intro assump_47 assump_48 =>
                apply False.elim assump_47
          let assump_43 := assump_26 assump_54
          apply False.elim assump_43


variable (p1 p7 p5 p3 : Prop)
theorem file82_16164 : (((((p5 → False) → (p5 ∧ True)) → ((p7 → True) ∨ (p3 ∨ p1))) → False) → False) := by
  intro assump_1
  have assump_12 : (((p5 → False) → (p5 ∧ True)) → ((p7 → True) ∨ (p3 ∨ p1))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    apply True.intro
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p6 p0 p2 p3 : Prop)
theorem file82_16545 : ((((((p3 ∨ p2) ∧ (p2 → False)) ∧ ((True ∨ p3) ∧ (p0 ∧ p6))) ∨ (((True → False) ∨ (True → False)) → ((False → True) → False))) → False) → False) := by
  intro assump_1
  have assump_26 : ((((p3 ∨ p2) ∧ (p2 → False)) ∧ ((True ∨ p3) ∧ (p0 ∧ p6))) ∨ (((True → False) ∨ (True → False)) → ((False → True) → False))) := by
    apply Or.inr
    intro assump_5
    intro assump_6
    cases assump_5
    case inl assump_9 =>
      have assump_27 : True := by
        apply True.intro
      let assump_13 := assump_9 assump_27
      apply False.elim assump_13
    case inr assump_10 =>
      have assump_28 : True := by
        apply True.intro
      let assump_19 := assump_10 assump_28
      apply False.elim assump_19
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p0 p4 p6 p3 p5 p1 p2 : Prop)
theorem file82_17383 : (((((p0 ∧ p1) → False) ∨ ((p5 → False) → (p3 ∧ p3))) → (((p1 → p4) ∧ (p1 → False)) ∨ ((p2 ∧ p6) → False))) → ((((p2 → False) → False) ∧ ((p4 ∨ p1) ∧ (p6 ∧ p2))) → (((False → False) ∧ (True → True)) ∨ ((p0 → False) → False)))) := by
  intro assump_42
  intro assump_43
  cases assump_43
  case intro assump_44 assump_45 =>
    cases assump_45
    case intro assump_48 assump_49 =>
      cases assump_48
      case inl assump_50 =>
        cases assump_49
        case intro assump_54 assump_55 =>
          apply Or.inl
          apply And.intro
          intro assump_62
          apply False.elim assump_62
          intro assump_65
          apply True.intro
      case inr assump_51 =>
        cases assump_49
        case intro assump_68 assump_69 =>
          apply Or.inl
          apply And.intro
          intro assump_76
          apply False.elim assump_76
          intro assump_79
          apply True.intro


variable (p6 p1 p5 : Prop)
theorem file82_18354 : (((((p5 ∧ p6) → False) → ((False ∧ p1) ∨ (False → False))) → (((True → False) → (False → False)) → False)) → False) := by
  intro assump_1
  have assump_19 : (((p5 ∧ p6) → False) → ((False ∧ p1) ∨ (False → False))) := by
    intro assump_5
    apply Or.inr
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_19
  have assump_20 : ((True → False) → (False → False)) := by
    intro assump_12
    intro assump_13
    apply False.elim assump_13
  let assump_11 := assump_4 assump_20
  apply False.elim assump_11


variable (p5 p2 p7 : Prop)
theorem file82_18946 : ((((((False ∧ p7) → (p2 → False)) ∧ ((p5 ∧ False) ∨ (True ∧ False))) → False) → False) → False) := by
  intro assump_9
  have assump_35 : ((((False ∧ p7) → (p2 → False)) ∧ ((p5 ∧ False) ∨ (True ∧ False))) → False) := by
    intro assump_13
    cases assump_13
    case intro assump_14 assump_15 =>
      cases assump_15
      case inl assump_18 =>
        cases assump_18
        case intro assump_20 assump_21 =>
          apply False.elim assump_21
      case inr assump_19 =>
        cases assump_19
        case intro assump_26 assump_27 =>
          apply False.elim assump_27
  let assump_12 := assump_9 assump_35
  apply False.elim assump_12


variable (p2 : Prop)
theorem file82_19640 : ((((((True ∨ p2) → (p2 → p2)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_25 : ((((True ∨ p2) → (p2 → p2)) → False) → False) := by
    intro assump_5
    have assump_26 : ((True ∨ p2) → (p2 → p2)) := by
      intro assump_9
      intro assump_10
      cases assump_9
      case inl assump_13 =>
        exact assump_10
      case inr assump_14 =>
        exact assump_14
    let assump_8 := assump_5 assump_26
    apply False.elim assump_8
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p0 p2 p7 : Prop)
theorem file82_20225 : (((((p2 ∧ False) → (False → False)) ∨ ((p0 → False) ∨ (p7 → False))) → False) → False) := by
  intro assump_15
  have assump_26 : (((p2 ∧ False) → (False → False)) ∨ ((p0 → False) ∨ (p7 → False))) := by
    apply Or.inl
    intro assump_19
    intro assump_20
    apply False.elim assump_20
  let assump_18 := assump_15 assump_26
  apply False.elim assump_18


variable (p6 p4 p3 p2 p5 p0 : Prop)
theorem file82_20644 : (((((p3 ∨ p5) → (p0 ∧ p5)) → ((p3 → False) → (True ∨ True))) ∨ (((p3 ∧ p5) → (False → p3)) → ((p6 → False) ∨ (p2 → p2)))) ∨ ((((p4 ∨ p4) → False) → ((p2 → p0) → False)) ∨ (((p6 ∧ False) ∨ (p6 → False)) ∨ ((p3 ∧ p2) ∧ (p0 → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  apply Or.inl
  apply True.intro


variable (p4 p1 p2 p5 p0 p7 p6 : Prop)
theorem file82_21045 : (((((p5 ∧ False) ∨ (p1 → False)) → False) ∨ (((p5 ∧ True) ∧ (True → False)) → ((p1 → False) → False))) → ((((p7 ∧ p4) ∧ (False → False)) → ((p4 ∨ p2) ∧ (False → False))) ∨ (((p0 ∨ p0) ∧ (False ∧ True)) ∨ ((p5 ∨ p6) → False)))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    apply And.intro
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        apply Or.inl
        exact assump_10
    intro assump_17
    apply False.elim assump_17
  case inr assump_3 =>
    apply Or.inl
    intro assump_22
    apply And.intro
    cases assump_22
    case intro assump_23 assump_24 =>
      cases assump_23
      case intro assump_25 assump_26 =>
        apply Or.inl
        exact assump_26
    intro assump_33
    apply False.elim assump_33


variable (p2 p5 p0 p1 p6 : Prop)
theorem file82_21955 : (((((p1 → False) → (False → False)) ∨ ((p6 → False) ∧ (p0 → False))) ∧ (((p0 ∧ True) ∨ (False → p5)) → False)) → ((((p0 ∨ p1) → False) ∧ ((False → False) ∧ (p2 ∧ p1))) ∨ (((p1 → False) ∧ (p0 ∧ p6)) → False))) := by
  intro assump_29
  cases assump_29
  case intro assump_30 assump_31 =>
    cases assump_30
    case inl assump_32 =>
      apply Or.inr
      intro assump_61
      cases assump_61
      case intro assump_62 assump_63 =>
        cases assump_63
        case intro assump_66 assump_67 =>
          have assump_128 : ((p0 ∧ True) ∨ (False → p5)) := by
            apply Or.inl
            apply And.intro
            exact assump_66
            apply True.intro
          let assump_75 := assump_31 assump_128
          apply False.elim assump_75
    case inr assump_33 =>
      cases assump_33
      case intro assump_79 assump_80 =>
        apply Or.inr
        intro assump_110
        cases assump_110
        case intro assump_111 assump_112 =>
          cases assump_112
          case intro assump_115 assump_116 =>
            have assump_129 : ((p0 ∧ True) ∨ (False → p5)) := by
              apply Or.inl
              apply And.intro
              exact assump_115
              apply True.intro
            let assump_124 := assump_31 assump_129
            apply False.elim assump_124


variable (p2 p5 p7 : Prop)
theorem file82_23317 : (((((p2 → False) → False) ∨ ((p7 → False) ∧ (True ∨ p5))) ∧ (((True → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_57 : ((True → False) → False) := by
        intro assump_11
        have assump_58 : True := by
          apply True.intro
        let assump_14 := assump_11 assump_58
        apply False.elim assump_14
      let assump_10 := assump_3 assump_57
      apply False.elim assump_10
    case inr assump_5 =>
      cases assump_5
      case intro assump_21 assump_22 =>
        cases assump_22
        case inl assump_25 =>
          have assump_59 : ((True → False) → False) := by
            intro assump_32
            have assump_60 : True := by
              apply True.intro
            let assump_35 := assump_32 assump_60
            apply False.elim assump_35
          let assump_31 := assump_3 assump_59
          apply False.elim assump_31
        case inr assump_26 =>
          have assump_61 : ((True → False) → False) := by
            intro assump_47
            have assump_62 : True := by
              apply True.intro
            let assump_50 := assump_47 assump_62
            apply False.elim assump_50
          let assump_46 := assump_3 assump_61
          apply False.elim assump_46


variable (p6 p2 p3 p5 p0 : Prop)
theorem file82_24719 : ((((((p2 ∧ p5) ∨ (p0 ∨ p6)) ∧ ((False ∧ p6) ∧ (False ∨ p3))) → False) → False) → False) := by
  intro assump_1
  have assump_43 : ((((p2 ∧ p5) ∨ (p0 ∨ p6)) ∧ ((False ∧ p6) ∧ (False ∨ p3))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_7
          case intro assump_16 assump_17 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              apply False.elim assump_18
      case inr assump_9 =>
        cases assump_9
        case inl assump_22 =>
          cases assump_7
          case intro assump_26 assump_27 =>
            cases assump_26
            case intro assump_28 assump_29 =>
              apply False.elim assump_28
        case inr assump_23 =>
          cases assump_7
          case intro assump_34 assump_35 =>
            cases assump_34
            case intro assump_36 assump_37 =>
              apply False.elim assump_36
  let assump_4 := assump_1 assump_43
  apply False.elim assump_4


variable (p5 p3 p2 p4 p7 p6 p0 : Prop)
theorem file82_25900 : ((((((p6 ∨ p4) ∧ (True → False)) → False) ∨ (((p3 ∨ p2) → False) ∨ ((p5 → False) ∨ (p7 ∨ p7)))) ∧ ((((p2 ∨ p0) ∨ (False → p6)) ∨ ((p4 ∧ p4) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_67 : (((p2 ∨ p0) ∨ (False → p6)) ∨ ((p4 ∧ p4) → False)) := by
        apply Or.inl
        apply Or.inr
        intro assump_11
        apply False.elim assump_11
      let assump_10 := assump_3 assump_67
      apply False.elim assump_10
    case inr assump_5 =>
      cases assump_5
      case inl assump_17 =>
        have assump_68 : (((p2 ∨ p0) ∨ (False → p6)) ∨ ((p4 ∧ p4) → False)) := by
          apply Or.inl
          apply Or.inr
          intro assump_24
          apply False.elim assump_24
        let assump_23 := assump_3 assump_68
        apply False.elim assump_23
      case inr assump_18 =>
        cases assump_18
        case inl assump_30 =>
          have assump_69 : (((p2 ∨ p0) ∨ (False → p6)) ∨ ((p4 ∧ p4) → False)) := by
            apply Or.inl
            apply Or.inr
            intro assump_37
            apply False.elim assump_37
          let assump_36 := assump_3 assump_69
          apply False.elim assump_36
        case inr assump_31 =>
          cases assump_31
          case inl assump_43 =>
            have assump_70 : (((p2 ∨ p0) ∨ (False → p6)) ∨ ((p4 ∧ p4) → False)) := by
              apply Or.inl
              apply Or.inr
              intro assump_50
              apply False.elim assump_50
            let assump_49 := assump_3 assump_70
            apply False.elim assump_49
          case inr assump_44 =>
            have assump_71 : (((p2 ∨ p0) ∨ (False → p6)) ∨ ((p4 ∧ p4) → False)) := by
              apply Or.inl
              apply Or.inr
              intro assump_61
              apply False.elim assump_61
            let assump_60 := assump_3 assump_71
            apply False.elim assump_60


variable (p4 p3 p2 p6 p7 p5 p1 : Prop)
theorem file82_27932 : (((((p4 → False) ∨ (p4 ∨ True)) ∧ ((p5 ∨ True) ∧ (p6 ∧ False))) ∧ (((p3 ∧ p6) ∨ (p1 ∧ p1)) → False)) → ((((p2 → p1) → (p1 ∧ p6)) ∨ ((p6 → p4) → False)) ∨ (((False ∧ True) ∨ (p4 → p3)) ∨ ((p7 ∧ p1) ∧ (p1 ∨ p6))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_5
        case intro assump_10 assump_11 =>
          cases assump_10
          case inl assump_12 =>
            cases assump_11
            case intro assump_16 assump_17 =>
              apply False.elim assump_17
          case inr assump_13 =>
            cases assump_11
            case intro assump_24 assump_25 =>
              apply False.elim assump_25
      case inr assump_7 =>
        cases assump_7
        case inl assump_30 =>
          cases assump_5
          case intro assump_34 assump_35 =>
            cases assump_34
            case inl assump_36 =>
              cases assump_35
              case intro assump_40 assump_41 =>
                apply False.elim assump_41
            case inr assump_37 =>
              cases assump_35
              case intro assump_48 assump_49 =>
                apply False.elim assump_49
        case inr assump_31 =>
          cases assump_5
          case intro assump_56 assump_57 =>
            cases assump_56
            case inl assump_58 =>
              cases assump_57
              case intro assump_62 assump_63 =>
                apply False.elim assump_63
            case inr assump_59 =>
              cases assump_57
              case intro assump_70 assump_71 =>
                apply False.elim assump_71


variable (p7 p1 p2 p3 : Prop)
theorem file82_29685 : ((((((p2 → False) → False) → False) → False) ∧ ((((p1 ∨ p3) ∧ (p3 → False)) → ((True → False) → (p2 → False))) → (((False → False) → (p7 → True)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_44 : (((p1 ∨ p3) ∧ (p3 → False)) → ((True → False) → (p2 → False))) := by
      intro assump_9
      intro assump_10
      intro assump_11
      cases assump_9
      case intro assump_16 assump_17 =>
        cases assump_16
        case inl assump_18 =>
          have assump_45 : True := by
            apply True.intro
          let assump_26 := assump_10 assump_45
          apply False.elim assump_26
        case inr assump_19 =>
          have assump_46 : p3 := by
            exact assump_19
          let assump_34 := assump_17 assump_46
          apply False.elim assump_34
    let assump_8 := assump_3 assump_44
    have assump_47 : ((False → False) → (p7 → True)) := by
      intro assump_39
      intro assump_40
      apply True.intro
    let assump_38 := assump_8 assump_47
    apply False.elim assump_38


variable (p4 p0 p1 p3 p2 p5 p7 : Prop)
theorem file82_30823 : ((((((p2 ∧ p2) ∨ (p2 ∨ p1)) ∨ ((p1 ∧ p5) → False)) ∧ (((True → p5) ∧ (p7 → p1)) ∧ ((p5 ∧ p4) → False))) ∧ ((((p2 ∧ p3) → (p5 ∧ p7)) → ((True → False) ∧ (p2 → p5))) ∧ (((False → p5) ∨ (p0 ∧ p2)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_8
          case intro assump_10 assump_11 =>
            cases assump_5
            case intro assump_16 assump_17 =>
              cases assump_16
              case intro assump_18 assump_19 =>
                cases assump_3
                case intro assump_26 assump_27 =>
                  have assump_116 : ((False → p5) ∨ (p0 ∧ p2)) := by
                    apply Or.inl
                    intro assump_33
                    apply False.elim assump_33
                  let assump_32 := assump_27 assump_116
                  apply False.elim assump_32
        case inr assump_9 =>
          cases assump_9
          case inl assump_39 =>
            cases assump_5
            case intro assump_43 assump_44 =>
              cases assump_43
              case intro assump_45 assump_46 =>
                cases assump_3
                case intro assump_53 assump_54 =>
                  have assump_117 : ((False → p5) ∨ (p0 ∧ p2)) := by
                    apply Or.inl
                    intro assump_60
                    apply False.elim assump_60
                  let assump_59 := assump_54 assump_117
                  apply False.elim assump_59
          case inr assump_40 =>
            cases assump_5
            case intro assump_68 assump_69 =>
              cases assump_68
              case intro assump_70 assump_71 =>
                cases assump_3
                case intro assump_78 assump_79 =>
                  have assump_118 : ((False → p5) ∨ (p0 ∧ p2)) := by
                    apply Or.inl
                    intro assump_85
                    apply False.elim assump_85
                  let assump_84 := assump_79 assump_118
                  apply False.elim assump_84
      case inr assump_7 =>
        cases assump_5
        case intro assump_93 assump_94 =>
          cases assump_93
          case intro assump_95 assump_96 =>
            cases assump_3
            case intro assump_103 assump_104 =>
              have assump_119 : ((False → p5) ∨ (p0 ∧ p2)) := by
                apply Or.inl
                intro assump_110
                apply False.elim assump_110
              let assump_109 := assump_104 assump_119
              apply False.elim assump_109


variable (p4 p0 p7 p2 p5 p6 p1 : Prop)
theorem file82_33574 : ((((((p1 → p1) → (p2 → p4)) → ((p6 ∨ p7) → False)) → (((True → False) → (p0 → False)) ∨ ((p5 → True) ∨ (False ∨ p7)))) → False) → False) := by
  intro assump_1
  have assump_21 : ((((p1 → p1) → (p2 → p4)) → ((p6 ∨ p7) → False)) → (((True → False) → (p0 → False)) ∨ ((p5 → True) ∨ (False ∨ p7)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    intro assump_9
    have assump_22 : True := by
      apply True.intro
    let assump_14 := assump_8 assump_22
    apply False.elim assump_14
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p0 p3 p5 p4 p1 p6 : Prop)
theorem file82_34201 : (((((False ∨ True) ∨ (p5 → p0)) ∨ ((p5 ∧ p1) ∨ (p0 → False))) ∧ (((p5 ∨ p6) ∨ (p3 ∧ p4)) ∧ ((False → p1) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          apply False.elim assump_8
        case inr assump_9 =>
          cases assump_3
          case intro assump_14 assump_15 =>
            cases assump_14
            case inl assump_16 =>
              cases assump_16
              case inl assump_18 =>
                have assump_198 : (False → p1) := by
                  intro assump_25
                  apply False.elim assump_25
                let assump_24 := assump_15 assump_198
                apply False.elim assump_24
              case inr assump_19 =>
                have assump_199 : (False → p1) := by
                  intro assump_36
                  apply False.elim assump_36
                let assump_35 := assump_15 assump_199
                apply False.elim assump_35
            case inr assump_17 =>
              cases assump_17
              case intro assump_42 assump_43 =>
                have assump_200 : (False → p1) := by
                  intro assump_51
                  apply False.elim assump_51
                let assump_50 := assump_15 assump_200
                apply False.elim assump_50
      case inr assump_7 =>
        cases assump_3
        case intro assump_59 assump_60 =>
          cases assump_59
          case inl assump_61 =>
            cases assump_61
            case inl assump_63 =>
              have assump_201 : (False → p1) := by
                intro assump_70
                apply False.elim assump_70
              let assump_69 := assump_60 assump_201
              apply False.elim assump_69
            case inr assump_64 =>
              have assump_202 : (False → p1) := by
                intro assump_81
                apply False.elim assump_81
              let assump_80 := assump_60 assump_202
              apply False.elim assump_80
          case inr assump_62 =>
            cases assump_62
            case intro assump_87 assump_88 =>
              have assump_203 : (False → p1) := by
                intro assump_96
                apply False.elim assump_96
              let assump_95 := assump_60 assump_203
              apply False.elim assump_95
    case inr assump_5 =>
      cases assump_5
      case inl assump_102 =>
        cases assump_102
        case intro assump_104 assump_105 =>
          cases assump_3
          case intro assump_110 assump_111 =>
            cases assump_110
            case inl assump_112 =>
              cases assump_112
              case inl assump_114 =>
                have assump_204 : (False → p1) := by
                  intro assump_121
                  apply False.elim assump_121
                let assump_120 := assump_111 assump_204
                apply False.elim assump_120
              case inr assump_115 =>
                have assump_205 : (False → p1) := by
                  intro assump_132
                  apply False.elim assump_132
                let assump_131 := assump_111 assump_205
                apply False.elim assump_131
            case inr assump_113 =>
              cases assump_113
              case intro assump_138 assump_139 =>
                have assump_206 : (False → p1) := by
                  intro assump_147
                  apply False.elim assump_147
                let assump_146 := assump_111 assump_206
                apply False.elim assump_146
      case inr assump_103 =>
        cases assump_3
        case intro assump_155 assump_156 =>
          cases assump_155
          case inl assump_157 =>
            cases assump_157
            case inl assump_159 =>
              have assump_207 : (False → p1) := by
                intro assump_166
                apply False.elim assump_166
              let assump_165 := assump_156 assump_207
              apply False.elim assump_165
            case inr assump_160 =>
              have assump_208 : (False → p1) := by
                intro assump_177
                apply False.elim assump_177
              let assump_176 := assump_156 assump_208
              apply False.elim assump_176
          case inr assump_158 =>
            cases assump_158
            case intro assump_183 assump_184 =>
              have assump_209 : (False → p1) := by
                intro assump_192
                apply False.elim assump_192
              let assump_191 := assump_156 assump_209
              apply False.elim assump_191


variable (p1 p4 p6 p7 p0 p5 p3 : Prop)
theorem file82_38952 : (((((p1 ∨ p6) ∧ (p0 → False)) → False) ∨ (((False → False) → (p0 ∧ p5)) ∧ ((False ∧ p3) → (p7 ∧ True)))) → ((((p7 → False) ∧ (p1 ∧ p3)) → ((p1 → False) ∧ (p0 → False))) → (((p6 → p1) → False) → ((False → False) ∨ (p4 → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_1
  case inl assump_8 =>
    apply Or.inl
    intro assump_12
    apply False.elim assump_12
  case inr assump_9 =>
    cases assump_9
    case intro assump_15 assump_16 =>
      apply Or.inl
      intro assump_21
      apply False.elim assump_21


variable (p2 p5 p7 p3 p4 : Prop)
theorem file82_39558 : (((((True → False) → (True ∨ True)) ∨ ((p5 ∧ p2) → False)) → False) → ((((p7 ∨ p3) ∨ (p4 ∨ p3)) → ((p4 ∧ p5) → False)) → False)) := by
  intro assump_1
  intro assump_2
  have assump_14 : (((True → False) → (True ∨ True)) ∨ ((p5 ∧ p2) → False)) := by
    apply Or.inl
    intro assump_8
    apply Or.inl
    apply True.intro
  let assump_7 := assump_1 assump_14
  apply False.elim assump_7


variable (p0 p1 p7 p2 p6 p5 p3 p4 : Prop)
theorem file82_40014 : (((((p7 ∧ p4) ∧ (p0 ∨ p1)) → ((p1 ∧ p2) → (p4 → p6))) → (((p1 → True) → False) ∨ ((p0 → False) → (p5 → p2)))) → ((((p5 ∧ p2) → (p6 → p4)) ∧ ((p7 → p1) ∨ (p3 → False))) → (((p0 ∧ p2) → False) → ((False → False) ∨ (p5 ∨ True))))) := by
  intro assump_23
  intro assump_24
  intro assump_25
  cases assump_24
  case intro assump_28 assump_29 =>
    cases assump_29
    case inl assump_32 =>
      apply Or.inl
      intro assump_38
      apply False.elim assump_38
    case inr assump_33 =>
      apply Or.inl
      intro assump_45
      apply False.elim assump_45


variable (p1 p2 p5 p7 p4 p6 : Prop)
theorem file82_40636 : ((((((p4 → False) → (p5 ∨ True)) → ((p2 ∨ p6) ∨ (p1 ∨ p4))) → (((p7 ∧ p6) → False) ∨ ((p2 → False) ∧ (True → p1)))) ∧ ((((False ∧ p1) ∨ (False ∨ False)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_25 : (((False ∧ p1) ∨ (False ∨ False)) → False) := by
      intro assump_9
      cases assump_9
      case inl assump_10 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          apply False.elim assump_12
      case inr assump_11 =>
        cases assump_11
        case inl assump_16 =>
          apply False.elim assump_16
        case inr assump_17 =>
          apply False.elim assump_17
    let assump_8 := assump_3 assump_25
    apply False.elim assump_8


variable (p4 p7 p1 p0 p5 p6 p2 : Prop)
theorem file82_41452 : (((((True → False) → (p1 ∨ p0)) ∨ ((False ∨ p7) → (False ∨ False))) ∨ (((False ∧ p4) ∧ (p0 ∧ True)) ∨ ((False → p7) → False))) ∨ ((((False → p5) → (p2 ∨ p6)) → False) → (((False → p0) → False) ∨ ((p4 ∨ p4) → False)))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  have assump_8 : True := by
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p6 p5 p1 p2 p7 p0 p3 p4 : Prop)
theorem file82_41918 : (((((p4 ∨ False) ∨ (p0 ∧ p7)) ∧ ((p6 ∨ p1) ∨ (p6 ∨ False))) ∧ (((p0 → p7) → (p6 ∨ p1)) → False)) → ((((p2 ∧ False) ∧ (p5 ∨ p3)) ∨ ((p7 ∨ p2) → False)) ∨ (((p1 → False) ∧ (p6 → p5)) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_5
          case inl assump_12 =>
            cases assump_12
            case inl assump_14 =>
              apply Or.inl
              apply Or.inr
              intro assump_20
              cases assump_20
              case inl assump_21 =>
                have assump_198 : ((p0 → p7) → (p6 ∨ p1)) := by
                  intro assump_27
                  apply Or.inl
                  exact assump_14
                let assump_26 := assump_3 assump_198
                apply False.elim assump_26
              case inr assump_22 =>
                have assump_199 : ((p0 → p7) → (p6 ∨ p1)) := by
                  intro assump_37
                  apply Or.inl
                  exact assump_14
                let assump_36 := assump_3 assump_199
                apply False.elim assump_36
            case inr assump_15 =>
              apply Or.inl
              apply Or.inr
              intro assump_47
              cases assump_47
              case inl assump_48 =>
                have assump_200 : ((p0 → p7) → (p6 ∨ p1)) := by
                  intro assump_54
                  apply Or.inr
                  exact assump_15
                let assump_53 := assump_3 assump_200
                apply False.elim assump_53
              case inr assump_49 =>
                have assump_201 : ((p0 → p7) → (p6 ∨ p1)) := by
                  intro assump_64
                  apply Or.inr
                  exact assump_15
                let assump_63 := assump_3 assump_201
                apply False.elim assump_63
          case inr assump_13 =>
            cases assump_13
            case inl assump_70 =>
              apply Or.inl
              apply Or.inr
              intro assump_76
              cases assump_76
              case inl assump_77 =>
                have assump_202 : ((p0 → p7) → (p6 ∨ p1)) := by
                  intro assump_83
                  apply Or.inl
                  exact assump_70
                let assump_82 := assump_3 assump_202
                apply False.elim assump_82
              case inr assump_78 =>
                have assump_203 : ((p0 → p7) → (p6 ∨ p1)) := by
                  intro assump_93
                  apply Or.inl
                  exact assump_70
                let assump_92 := assump_3 assump_203
                apply False.elim assump_92
            case inr assump_71 =>
              apply False.elim assump_71
        case inr assump_9 =>
          apply False.elim assump_9
      case inr assump_7 =>
        cases assump_7
        case intro assump_103 assump_104 =>
          cases assump_5
          case inl assump_109 =>
            cases assump_109
            case inl assump_111 =>
              apply Or.inl
              apply Or.inr
              intro assump_117
              cases assump_117
              case inl assump_118 =>
                have assump_204 : ((p0 → p7) → (p6 ∨ p1)) := by
                  intro assump_124
                  apply Or.inl
                  exact assump_111
                let assump_123 := assump_3 assump_204
                apply False.elim assump_123
              case inr assump_119 =>
                have assump_205 : ((p0 → p7) → (p6 ∨ p1)) := by
                  intro assump_134
                  apply Or.inl
                  exact assump_111
                let assump_133 := assump_3 assump_205
                apply False.elim assump_133
            case inr assump_112 =>
              apply Or.inl
              apply Or.inr
              intro assump_144
              cases assump_144
              case inl assump_145 =>
                have assump_206 : ((p0 → p7) → (p6 ∨ p1)) := by
                  intro assump_151
                  apply Or.inr
                  exact assump_112
                let assump_150 := assump_3 assump_206
                apply False.elim assump_150
              case inr assump_146 =>
                have assump_207 : ((p0 → p7) → (p6 ∨ p1)) := by
                  intro assump_161
                  apply Or.inr
                  exact assump_112
                let assump_160 := assump_3 assump_207
                apply False.elim assump_160
          case inr assump_110 =>
            cases assump_110
            case inl assump_167 =>
              apply Or.inl
              apply Or.inr
              intro assump_173
              cases assump_173
              case inl assump_174 =>
                have assump_208 : ((p0 → p7) → (p6 ∨ p1)) := by
                  intro assump_180
                  apply Or.inl
                  exact assump_167
                let assump_179 := assump_3 assump_208
                apply False.elim assump_179
              case inr assump_175 =>
                have assump_209 : ((p0 → p7) → (p6 ∨ p1)) := by
                  intro assump_190
                  apply Or.inl
                  exact assump_167
                let assump_189 := assump_3 assump_209
                apply False.elim assump_189
            case inr assump_168 =>
              apply False.elim assump_168


variable (p1 p4 p2 p3 p0 p6 p7 p5 : Prop)
theorem file82_47477 : (((((p5 ∨ p4) ∨ (False → p1)) ∨ ((p6 → False) ∧ (True ∨ p6))) → False) → ((((p6 → p3) ∨ (p7 ∨ p5)) ∧ ((True → p5) ∧ (True ∨ p6))) ∧ (((p1 → False) → (p2 ∧ p3)) ∨ ((p7 ∨ p0) → (p1 ∨ p4))))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  apply Or.inl
  intro assump_4
  have assump_52 : (((p5 ∨ p4) ∨ (False → p1)) ∨ ((p6 → False) ∧ (True ∨ p6))) := by
    apply Or.inl
    apply Or.inr
    intro assump_9
    apply False.elim assump_9
  let assump_8 := assump_1 assump_52
  apply False.elim assump_8
  apply And.intro
  intro assump_15
  have assump_53 : (((p5 ∨ p4) ∨ (False → p1)) ∨ ((p6 → False) ∧ (True ∨ p6))) := by
    apply Or.inl
    apply Or.inr
    intro assump_21
    apply False.elim assump_21
  let assump_20 := assump_1 assump_53
  apply False.elim assump_20
  apply Or.inl
  apply True.intro
  apply Or.inl
  intro assump_31
  apply And.intro
  have assump_54 : (((p5 ∨ p4) ∨ (False → p1)) ∨ ((p6 → False) ∧ (True ∨ p6))) := by
    apply Or.inl
    apply Or.inr
    intro assump_36
    apply False.elim assump_36
  let assump_35 := assump_1 assump_54
  apply False.elim assump_35
  have assump_55 : (((p5 ∨ p4) ∨ (False → p1)) ∨ ((p6 → False) ∧ (True ∨ p6))) := by
    apply Or.inl
    apply Or.inr
    intro assump_46
    apply False.elim assump_46
  let assump_45 := assump_1 assump_55
  apply False.elim assump_45


variable (p7 p1 p4 p2 p0 : Prop)
theorem file82_48879 : ((((((False → False) → (True → False)) → False) ∨ (((p7 ∧ p2) ∨ (p0 → False)) → ((p4 ∨ p1) → (p0 ∧ p7)))) → False) → False) := by
  intro assump_1
  have assump_19 : ((((False → False) → (True → False)) → False) ∨ (((p7 ∧ p2) ∨ (p0 → False)) → ((p4 ∨ p1) → (p0 ∧ p7)))) := by
    apply Or.inl
    intro assump_5
    have assump_20 : (False → False) := by
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_20
    have assump_21 : True := by
      apply True.intro
    let assump_12 := assump_8 assump_21
    apply False.elim assump_12
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p2 p6 p1 p7 p4 p0 : Prop)
theorem file82_49577 : ((((((True ∧ p1) ∧ (p7 ∧ False)) → ((p6 ∧ p4) → (p1 → p1))) ∨ (((p0 → True) ∨ (p7 → False)) ∨ ((p0 ∨ p2) → False))) → False) → False) := by
  intro assump_1
  have assump_33 : ((((True ∧ p1) ∧ (p7 ∧ False)) → ((p6 ∧ p4) → (p1 → p1))) ∨ (((p0 → True) ∨ (p7 → False)) ∨ ((p0 ∨ p2) → False))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      cases assump_5
      case intro assump_16 assump_17 =>
        cases assump_16
        case intro assump_18 assump_19 =>
          cases assump_17
          case intro assump_24 assump_25 =>
            apply False.elim assump_25
  let assump_4 := assump_1 assump_33
  apply False.elim assump_4


variable (p1 p4 p0 p5 p6 p2 : Prop)
theorem file82_50365 : (((((p5 ∧ False) → False) → ((True → False) → False)) → False) → ((((p0 → p1) ∨ (p5 ∨ True)) ∧ ((False ∨ p2) ∧ (p5 ∧ p5))) ∧ (((p6 ∨ p6) ∧ (p4 ∧ p0)) → ((True ∨ p6) → False)))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  apply Or.inl
  intro assump_4
  have assump_190 : (((p5 ∧ False) → False) → ((True → False) → False)) := by
    intro assump_9
    intro assump_10
    have assump_191 : True := by
      apply True.intro
    let assump_16 := assump_10 assump_191
    apply False.elim assump_16
  let assump_8 := assump_1 assump_190
  apply False.elim assump_8
  apply And.intro
  have assump_192 : (((p5 ∧ False) → False) → ((True → False) → False)) := by
    intro assump_26
    intro assump_27
    have assump_193 : True := by
      apply True.intro
    let assump_33 := assump_27 assump_193
    apply False.elim assump_33
  let assump_25 := assump_1 assump_192
  apply False.elim assump_25
  apply And.intro
  have assump_194 : (((p5 ∧ False) → False) → ((True → False) → False)) := by
    intro assump_43
    intro assump_44
    have assump_195 : True := by
      apply True.intro
    let assump_50 := assump_44 assump_195
    apply False.elim assump_50
  let assump_42 := assump_1 assump_194
  apply False.elim assump_42
  have assump_196 : (((p5 ∧ False) → False) → ((True → False) → False)) := by
    intro assump_60
    intro assump_61
    have assump_197 : True := by
      apply True.intro
    let assump_67 := assump_61 assump_197
    apply False.elim assump_67
  let assump_59 := assump_1 assump_196
  apply False.elim assump_59
  intro assump_74
  intro assump_75
  cases assump_75
  case inl assump_76 =>
    cases assump_74
    case intro assump_80 assump_81 =>
      cases assump_80
      case inl assump_82 =>
        cases assump_81
        case intro assump_86 assump_87 =>
          have assump_198 : (((p5 ∧ False) → False) → ((True → False) → False)) := by
            intro assump_95
            intro assump_96
            have assump_199 : True := by
              apply True.intro
            let assump_102 := assump_96 assump_199
            apply False.elim assump_102
          let assump_94 := assump_1 assump_198
          apply False.elim assump_94
      case inr assump_83 =>
        cases assump_81
        case intro assump_111 assump_112 =>
          have assump_200 : (((p5 ∧ False) → False) → ((True → False) → False)) := by
            intro assump_120
            intro assump_121
            have assump_201 : True := by
              apply True.intro
            let assump_127 := assump_121 assump_201
            apply False.elim assump_127
          let assump_119 := assump_1 assump_200
          apply False.elim assump_119
  case inr assump_77 =>
    cases assump_74
    case intro assump_136 assump_137 =>
      cases assump_136
      case inl assump_138 =>
        cases assump_137
        case intro assump_142 assump_143 =>
          have assump_202 : (((p5 ∧ False) → False) → ((True → False) → False)) := by
            intro assump_151
            intro assump_152
            have assump_203 : True := by
              apply True.intro
            let assump_158 := assump_152 assump_203
            apply False.elim assump_158
          let assump_150 := assump_1 assump_202
          apply False.elim assump_150
      case inr assump_139 =>
        cases assump_137
        case intro assump_167 assump_168 =>
          have assump_204 : (((p5 ∧ False) → False) → ((True → False) → False)) := by
            intro assump_176
            intro assump_177
            have assump_205 : True := by
              apply True.intro
            let assump_183 := assump_177 assump_205
            apply False.elim assump_183
          let assump_175 := assump_1 assump_204
          apply False.elim assump_175


variable (p2 p4 p5 p7 p1 p0 p6 p3 : Prop)
theorem file82_54214 : (((((p1 ∧ p2) → False) ∨ ((True → p3) ∨ (p6 ∧ True))) → (((False ∧ p7) ∧ (False → False)) → False)) ∨ ((((p5 → p7) → (p7 → p4)) → False) ∧ (((p0 ∨ p7) → (p1 ∨ True)) → ((p3 → p6) → False)))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      apply False.elim assump_5


variable (p5 p6 p4 p2 : Prop)
theorem file82_54652 : ((((((False ∧ p6) ∨ (p6 ∧ False)) → ((p4 → p2) → False)) ∨ (((p5 ∨ True) → False) ∨ ((p5 → p6) → (p5 ∧ False)))) → False) → False) := by
  intro assump_10
  have assump_33 : ((((False ∧ p6) ∨ (p6 ∧ False)) → ((p4 → p2) → False)) ∨ (((p5 ∨ True) → False) ∨ ((p5 → p6) → (p5 ∧ False)))) := by
    apply Or.inl
    intro assump_14
    intro assump_15
    cases assump_14
    case inl assump_18 =>
      cases assump_18
      case intro assump_20 assump_21 =>
        apply False.elim assump_20
    case inr assump_19 =>
      cases assump_19
      case intro assump_24 assump_25 =>
        apply False.elim assump_25
  let assump_13 := assump_10 assump_33
  apply False.elim assump_13


variable (p2 p4 p6 p3 p1 p5 : Prop)
theorem file82_55394 : ((((((p2 ∨ p1) ∧ (p6 → False)) ∧ ((True → False) → (True → False))) ∨ (((p5 ∧ p3) ∨ (p1 → False)) ∧ ((p3 ∧ p5) → False))) ∧ ((((p4 ∨ p3) → (p2 → p3)) ∨ ((p4 ∧ p5) → (p6 → False))) ∧ (((p6 ∨ p2) ∨ (False ∨ True)) ∧ ((p6 → True) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_8
          case inl assump_10 =>
            cases assump_3
            case intro assump_18 assump_19 =>
              cases assump_18
              case inl assump_20 =>
                cases assump_19
                case intro assump_24 assump_25 =>
                  cases assump_24
                  case inl assump_26 =>
                    cases assump_26
                    case inl assump_28 =>
                      have assump_368 : (p6 → True) := by
                        intro assump_35
                        apply True.intro
                      let assump_34 := assump_25 assump_368
                      apply False.elim assump_34
                    case inr assump_29 =>
                      have assump_369 : (p6 → True) := by
                        intro assump_44
                        apply True.intro
                      let assump_43 := assump_25 assump_369
                      apply False.elim assump_43
                  case inr assump_27 =>
                    cases assump_27
                    case inl assump_48 =>
                      apply False.elim assump_48
                    case inr assump_49 =>
                      have assump_370 : (p6 → True) := by
                        intro assump_57
                        apply True.intro
                      let assump_56 := assump_25 assump_370
                      apply False.elim assump_56
              case inr assump_21 =>
                cases assump_19
                case intro assump_63 assump_64 =>
                  cases assump_63
                  case inl assump_65 =>
                    cases assump_65
                    case inl assump_67 =>
                      have assump_371 : (p6 → True) := by
                        intro assump_74
                        apply True.intro
                      let assump_73 := assump_64 assump_371
                      apply False.elim assump_73
                    case inr assump_68 =>
                      have assump_372 : (p6 → True) := by
                        intro assump_83
                        apply True.intro
                      let assump_82 := assump_64 assump_372
                      apply False.elim assump_82
                  case inr assump_66 =>
                    cases assump_66
                    case inl assump_87 =>
                      apply False.elim assump_87
                    case inr assump_88 =>
                      have assump_373 : (p6 → True) := by
                        intro assump_96
                        apply True.intro
                      let assump_95 := assump_64 assump_373
                      apply False.elim assump_95
          case inr assump_11 =>
            cases assump_3
            case intro assump_106 assump_107 =>
              cases assump_106
              case inl assump_108 =>
                cases assump_107
                case intro assump_112 assump_113 =>
                  cases assump_112
                  case inl assump_114 =>
                    cases assump_114
                    case inl assump_116 =>
                      have assump_374 : (p6 → True) := by
                        intro assump_123
                        apply True.intro
                      let assump_122 := assump_113 assump_374
                      apply False.elim assump_122
                    case inr assump_117 =>
                      have assump_375 : (p6 → True) := by
                        intro assump_132
                        apply True.intro
                      let assump_131 := assump_113 assump_375
                      apply False.elim assump_131
                  case inr assump_115 =>
                    cases assump_115
                    case inl assump_136 =>
                      apply False.elim assump_136
                    case inr assump_137 =>
                      have assump_376 : (p6 → True) := by
                        intro assump_145
                        apply True.intro
                      let assump_144 := assump_113 assump_376
                      apply False.elim assump_144
              case inr assump_109 =>
                cases assump_107
                case intro assump_151 assump_152 =>
                  cases assump_151
                  case inl assump_153 =>
                    cases assump_153
                    case inl assump_155 =>
                      have assump_377 : (p6 → True) := by
                        intro assump_162
                        apply True.intro
                      let assump_161 := assump_152 assump_377
                      apply False.elim assump_161
                    case inr assump_156 =>
                      have assump_378 : (p6 → True) := by
                        intro assump_171
                        apply True.intro
                      let assump_170 := assump_152 assump_378
                      apply False.elim assump_170
                  case inr assump_154 =>
                    cases assump_154
                    case inl assump_175 =>
                      apply False.elim assump_175
                    case inr assump_176 =>
                      have assump_379 : (p6 → True) := by
                        intro assump_184
                        apply True.intro
                      let assump_183 := assump_152 assump_379
                      apply False.elim assump_183
    case inr assump_5 =>
      cases assump_5
      case intro assump_188 assump_189 =>
        cases assump_188
        case inl assump_190 =>
          cases assump_190
          case intro assump_192 assump_193 =>
            cases assump_3
            case intro assump_200 assump_201 =>
              cases assump_200
              case inl assump_202 =>
                cases assump_201
                case intro assump_206 assump_207 =>
                  cases assump_206
                  case inl assump_208 =>
                    cases assump_208
                    case inl assump_210 =>
                      have assump_380 : (p6 → True) := by
                        intro assump_217
                        apply True.intro
                      let assump_216 := assump_207 assump_380
                      apply False.elim assump_216
                    case inr assump_211 =>
                      have assump_381 : (p6 → True) := by
                        intro assump_226
                        apply True.intro
                      let assump_225 := assump_207 assump_381
                      apply False.elim assump_225
                  case inr assump_209 =>
                    cases assump_209
                    case inl assump_230 =>
                      apply False.elim assump_230
                    case inr assump_231 =>
                      have assump_382 : (p6 → True) := by
                        intro assump_239
                        apply True.intro
                      let assump_238 := assump_207 assump_382
                      apply False.elim assump_238
              case inr assump_203 =>
                cases assump_201
                case intro assump_245 assump_246 =>
                  cases assump_245
                  case inl assump_247 =>
                    cases assump_247
                    case inl assump_249 =>
                      have assump_383 : (p6 → True) := by
                        intro assump_256
                        apply True.intro
                      let assump_255 := assump_246 assump_383
                      apply False.elim assump_255
                    case inr assump_250 =>
                      have assump_384 : (p6 → True) := by
                        intro assump_265
                        apply True.intro
                      let assump_264 := assump_246 assump_384
                      apply False.elim assump_264
                  case inr assump_248 =>
                    cases assump_248
                    case inl assump_269 =>
                      apply False.elim assump_269
                    case inr assump_270 =>
                      have assump_385 : (p6 → True) := by
                        intro assump_278
                        apply True.intro
                      let assump_277 := assump_246 assump_385
                      apply False.elim assump_277
        case inr assump_191 =>
          cases assump_3
          case intro assump_286 assump_287 =>
            cases assump_286
            case inl assump_288 =>
              cases assump_287
              case intro assump_292 assump_293 =>
                cases assump_292
                case inl assump_294 =>
                  cases assump_294
                  case inl assump_296 =>
                    have assump_386 : (p6 → True) := by
                      intro assump_303
                      apply True.intro
                    let assump_302 := assump_293 assump_386
                    apply False.elim assump_302
                  case inr assump_297 =>
                    have assump_387 : (p6 → True) := by
                      intro assump_312
                      apply True.intro
                    let assump_311 := assump_293 assump_387
                    apply False.elim assump_311
                case inr assump_295 =>
                  cases assump_295
                  case inl assump_316 =>
                    apply False.elim assump_316
                  case inr assump_317 =>
                    have assump_388 : (p6 → True) := by
                      intro assump_325
                      apply True.intro
                    let assump_324 := assump_293 assump_388
                    apply False.elim assump_324
            case inr assump_289 =>
              cases assump_287
              case intro assump_331 assump_332 =>
                cases assump_331
                case inl assump_333 =>
                  cases assump_333
                  case inl assump_335 =>
                    have assump_389 : (p6 → True) := by
                      intro assump_342
                      apply True.intro
                    let assump_341 := assump_332 assump_389
                    apply False.elim assump_341
                  case inr assump_336 =>
                    have assump_390 : (p6 → True) := by
                      intro assump_351
                      apply True.intro
                    let assump_350 := assump_332 assump_390
                    apply False.elim assump_350
                case inr assump_334 =>
                  cases assump_334
                  case inl assump_355 =>
                    apply False.elim assump_355
                  case inr assump_356 =>
                    have assump_391 : (p6 → True) := by
                      intro assump_364
                      apply True.intro
                    let assump_363 := assump_332 assump_391
                    apply False.elim assump_363


variable (p3 p5 p1 p7 p4 : Prop)
theorem file82_66855 : (((((p7 ∧ p7) → False) ∧ ((p3 ∧ p1) → (p3 → p1))) → False) → ((((p7 → p7) ∨ (p4 ∨ True)) ∧ ((False ∧ p1) ∧ (p5 → p5))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_4
      case intro assump_9 assump_10 =>
        cases assump_9
        case intro assump_11 assump_12 =>
          apply False.elim assump_11
    case inr assump_6 =>
      cases assump_6
      case inl assump_15 =>
        cases assump_4
        case intro assump_19 assump_20 =>
          cases assump_19
          case intro assump_21 assump_22 =>
            apply False.elim assump_21
      case inr assump_16 =>
        cases assump_4
        case intro assump_27 assump_28 =>
          cases assump_27
          case intro assump_29 assump_30 =>
            apply False.elim assump_29


variable (p5 p2 p3 p0 p4 p6 : Prop)
theorem file82_67791 : ((((((False → False) → False) → ((p6 → p0) ∨ (p6 ∨ p6))) ∨ (((p4 ∨ p5) → (p3 ∧ p4)) ∧ ((p2 → False) ∨ (False → False)))) → False) → False) := by
  intro assump_1
  have assump_22 : ((((False → False) → False) → ((p6 → p0) ∨ (p6 ∨ p6))) ∨ (((p4 ∨ p5) → (p3 ∧ p4)) ∧ ((p2 → False) ∨ (False → False)))) := by
    apply Or.inl
    intro assump_5
    apply Or.inl
    intro assump_8
    have assump_23 : (False → False) := by
      intro assump_13
      apply False.elim assump_13
    let assump_12 := assump_5 assump_23
    apply False.elim assump_12
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p2 p7 p4 p5 : Prop)
theorem file82_68457 : (((((p7 → False) ∧ (False ∨ True)) → ((p2 → False) ∨ (p2 → False))) ∧ (((p4 ∧ True) → (p5 → p5)) → False)) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    have assump_26 : ((p4 ∧ True) → (p5 → p5)) := by
      intro assump_13
      intro assump_14
      cases assump_13
      case intro assump_17 assump_18 =>
        exact assump_14
    let assump_12 := assump_7 assump_26
    apply False.elim assump_12


variable (p0 p6 p2 p4 p3 : Prop)
theorem file82_68958 : ((((((False → False) → False) ∧ ((p0 → False) ∧ (p4 ∨ p2))) → (((p2 ∧ p2) ∧ (p3 → True)) ∧ ((p6 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_91 : ((((False → False) → False) ∧ ((p0 → False) ∧ (p4 ∨ p2))) → (((p2 ∧ p2) ∧ (p3 → True)) ∧ ((p6 → False) → False))) := by
    intro assump_5
    apply And.intro
    apply And.intro
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_11
        case inl assump_14 =>
          have assump_92 : (False → False) := by
            intro assump_21
            apply False.elim assump_21
          let assump_20 := assump_6 assump_92
          apply False.elim assump_20
        case inr assump_15 =>
          exact assump_15
    cases assump_5
    case intro assump_29 assump_30 =>
      cases assump_30
      case intro assump_33 assump_34 =>
        cases assump_34
        case inl assump_37 =>
          have assump_93 : (False → False) := by
            intro assump_44
            apply False.elim assump_44
          let assump_43 := assump_29 assump_93
          apply False.elim assump_43
        case inr assump_38 =>
          exact assump_38
    intro assump_52
    apply True.intro
    intro assump_53
    cases assump_5
    case intro assump_56 assump_57 =>
      cases assump_57
      case intro assump_60 assump_61 =>
        cases assump_61
        case inl assump_64 =>
          have assump_94 : (False → False) := by
            intro assump_71
            apply False.elim assump_71
          let assump_70 := assump_56 assump_94
          apply False.elim assump_70
        case inr assump_65 =>
          have assump_95 : (False → False) := by
            intro assump_82
            apply False.elim assump_82
          let assump_81 := assump_56 assump_95
          apply False.elim assump_81
  let assump_4 := assump_1 assump_91
  apply False.elim assump_4


variable (p1 p0 p7 p3 p4 p5 p6 : Prop)
theorem file82_70979 : (((((p4 → p1) → (p4 ∨ True)) → False) → (((False → p3) → False) ∨ ((p5 → p0) → (p1 → False)))) ∨ ((((p6 ∨ False) → (p3 ∧ p6)) → ((p4 ∨ False) → False)) ∨ (((p1 ∨ p5) → False) ∨ ((p7 → False) → False)))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_15 : ((p4 → p1) → (p4 ∨ True)) := by
    intro assump_9
    apply Or.inr
    apply True.intro
  let assump_8 := assump_1 assump_15
  apply False.elim assump_8


variable (p6 p1 p5 p3 : Prop)
theorem file82_71479 : (((((p5 → p5) → False) → ((p6 ∨ p1) → False)) → False) → ((((p3 ∧ False) ∨ (False → p5)) → False) ∨ (((p5 ∧ p5) → False) ∨ ((p3 → p3) ∨ (False → False))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case inl assump_5 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      apply False.elim assump_8
  case inr assump_6 =>
    have assump_46 : (((p5 → p5) → False) → ((p6 ∨ p1) → False)) := by
      intro assump_17
      intro assump_18
      cases assump_18
      case inl assump_19 =>
        have assump_47 : (p5 → p5) := by
          intro assump_26
          exact assump_26
        let assump_25 := assump_17 assump_47
        apply False.elim assump_25
      case inr assump_20 =>
        have assump_48 : (p5 → p5) := by
          intro assump_37
          exact assump_37
        let assump_36 := assump_17 assump_48
        apply False.elim assump_36
    let assump_16 := assump_1 assump_46
    apply False.elim assump_16


variable (p3 p7 p2 p1 p5 p4 p0 p6 : Prop)
theorem file82_72516 : (((((p5 → p7) → (p0 ∨ p4)) → False) ∨ (((p0 → False) ∧ (p7 → False)) → ((p6 ∧ p3) ∧ (False → p5)))) → ((((p0 → False) → (p6 ∨ True)) ∨ ((p1 ∨ p4) → (p7 → p1))) ∨ (((p6 ∨ p1) ∧ (p2 ∨ p1)) ∨ ((p7 ∨ p6) → False)))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply Or.inl
    intro assump_6
    apply Or.inr
    apply True.intro
  case inr assump_3 =>
    apply Or.inl
    apply Or.inl
    intro assump_11
    apply Or.inr
    apply True.intro


variable (p0 p6 p7 p1 p2 p4 p5 : Prop)
theorem file82_73060 : (((((p0 ∧ False) ∨ (p6 ∧ p0)) ∨ ((p7 ∧ p5) ∧ (p6 ∧ p6))) → (((p6 ∧ p4) ∨ (p5 ∨ True)) ∨ ((p2 ∨ p6) ∨ (p5 ∧ p2)))) ∨ ((((p1 ∨ p6) → (False → p4)) → ((p2 → False) → False)) ∧ (((p5 → True) ∧ (p2 ∧ p5)) → ((True ∨ p1) ∨ (p0 ∧ p7))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        apply False.elim assump_7
    case inr assump_5 =>
      cases assump_5
      case intro assump_12 assump_13 =>
        apply Or.inl
        apply Or.inr
        apply Or.inr
        apply True.intro
  case inr assump_3 =>
    cases assump_3
    case intro assump_18 assump_19 =>
      cases assump_18
      case intro assump_20 assump_21 =>
        cases assump_19
        case intro assump_26 assump_27 =>
          apply Or.inl
          apply Or.inr
          apply Or.inl
          exact assump_21


variable (p4 p1 p2 p0 p6 p5 : Prop)
theorem file82_74043 : ((((((p5 ∧ False) ∧ (p2 → False)) → ((False ∨ p0) → (p0 ∧ p2))) ∨ (((p1 ∧ p6) → (p1 ∨ p4)) → ((p1 ∨ p4) → False))) → False) → False) := by
  intro assump_1
  have assump_38 : ((((p5 ∧ False) ∧ (p2 → False)) → ((False ∨ p0) → (p0 ∧ p2))) ∨ (((p1 ∧ p6) → (p1 ∨ p4)) → ((p1 ∨ p4) → False))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    apply And.intro
    cases assump_6
    case inl assump_7 =>
      apply False.elim assump_7
    case inr assump_8 =>
      cases assump_5
      case intro assump_13 assump_14 =>
        cases assump_13
        case intro assump_15 assump_16 =>
          apply False.elim assump_16
    cases assump_6
    case inl assump_21 =>
      apply False.elim assump_21
    case inr assump_22 =>
      cases assump_5
      case intro assump_27 assump_28 =>
        cases assump_27
        case intro assump_29 assump_30 =>
          apply False.elim assump_30
  let assump_4 := assump_1 assump_38
  apply False.elim assump_4


variable (p4 : Prop)
theorem file82_75055 : (((((p4 → p4) → (False ∨ False)) → False) → False) → False) := by
  intro assump_1
  have assump_22 : (((p4 → p4) → (False ∨ False)) → False) := by
    intro assump_5
    have assump_23 : (p4 → p4) := by
      intro assump_9
      exact assump_9
    let assump_8 := assump_5 assump_23
    cases assump_8
    case inl assump_13 =>
      apply False.elim assump_13
    case inr assump_14 =>
      apply False.elim assump_14
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p0 p3 p6 p5 : Prop)
theorem file82_75596 : (((((True → False) → (True ∨ p0)) → False) ∧ (((p5 ∨ p3) ∧ (p5 ∧ True)) ∨ ((True → False) ∧ (p6 ∨ False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_9
          case intro assump_14 assump_15 =>
            have assump_61 : ((True → False) → (True ∨ p0)) := by
              intro assump_23
              apply Or.inl
              apply True.intro
            let assump_22 := assump_2 assump_61
            apply False.elim assump_22
        case inr assump_11 =>
          cases assump_9
          case intro assump_31 assump_32 =>
            have assump_62 : ((True → False) → (True ∨ p0)) := by
              intro assump_40
              apply Or.inl
              apply True.intro
            let assump_39 := assump_2 assump_62
            apply False.elim assump_39
    case inr assump_7 =>
      cases assump_7
      case intro assump_46 assump_47 =>
        cases assump_47
        case inl assump_50 =>
          have assump_63 : True := by
            apply True.intro
          let assump_55 := assump_46 assump_63
          apply False.elim assump_55
        case inr assump_51 =>
          apply False.elim assump_51


variable (p6 p7 p3 p0 p2 : Prop)
theorem file82_77008 : ((((((True ∨ p2) → False) → ((p6 → False) ∨ (p6 ∨ p0))) → (((p2 → True) → (p6 → p6)) ∨ ((p3 ∨ p7) → False))) → False) → False) := by
  intro assump_1
  have assump_17 : ((((True ∨ p2) → False) → ((p6 → False) ∨ (p6 ∨ p0))) → (((p2 → True) → (p6 → p6)) ∨ ((p3 ∨ p7) → False))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    intro assump_9
    exact assump_9
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p7 p4 p6 p2 p5 p0 : Prop)
theorem file82_77508 : ((((((p4 ∨ True) → False) → False) ∧ (((p4 → p6) → False) ∧ ((p5 → p4) ∨ (p5 → False)))) ∧ ((((p2 ∨ p6) → False) → ((False → p7) ∧ (p0 → p0))) → (((p4 → False) ∧ (p4 → p2)) ∧ ((p0 ∧ p2) ∧ (p4 ∧ p4))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_9
        case inl assump_12 =>
          have assump_114 : (p4 → p6) := by
            intro assump_41
            have assump_115 : (((p2 ∨ p6) → False) → ((False → p7) ∧ (p0 → p0))) := by
              intro assump_46
              apply And.intro
              intro assump_47
              apply False.elim assump_47
              intro assump_50
              exact assump_50
            let assump_45 := assump_3 assump_115
            let assump_55 := And.left assump_45
            let assump_56 := And.left assump_55
            have assump_116 : p4 := by
              exact assump_41
            let assump_57 := assump_56 assump_116
            apply False.elim assump_57
          let assump_40 := assump_8 assump_114
          apply False.elim assump_40
        case inr assump_13 =>
          have assump_117 : (p4 → p6) := by
            intro assump_91
            have assump_118 : (((p2 ∨ p6) → False) → ((False → p7) ∧ (p0 → p0))) := by
              intro assump_96
              apply And.intro
              intro assump_97
              apply False.elim assump_97
              intro assump_100
              exact assump_100
            let assump_95 := assump_3 assump_118
            let assump_105 := And.left assump_95
            let assump_106 := And.left assump_105
            have assump_119 : p4 := by
              exact assump_91
            let assump_107 := assump_106 assump_119
            apply False.elim assump_107
          let assump_90 := assump_8 assump_117
          apply False.elim assump_90


variable (p2 p6 p3 p5 : Prop)
theorem file82_79526 : ((((((p5 → False) ∧ (p5 ∧ p6)) ∧ ((p3 → p2) ∨ (True ∨ p3))) → False) → False) → False) := by
  intro assump_1
  have assump_51 : ((((p5 → False) ∧ (p5 ∧ p6)) ∧ ((p3 → p2) ∨ (True ∨ p3))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          cases assump_7
          case inl assump_18 =>
            have assump_52 : p5 := by
              exact assump_12
            let assump_25 := assump_8 assump_52
            apply False.elim assump_25
          case inr assump_19 =>
            cases assump_19
            case inl assump_29 =>
              have assump_53 : p5 := by
                exact assump_12
              let assump_35 := assump_8 assump_53
              apply False.elim assump_35
            case inr assump_30 =>
              have assump_54 : p5 := by
                exact assump_12
              let assump_44 := assump_8 assump_54
              apply False.elim assump_44
  let assump_4 := assump_1 assump_51
  apply False.elim assump_4


variable (p2 p0 p5 p6 : Prop)
theorem file82_80711 : (((((p2 ∨ True) → False) ∧ ((False ∨ p0) → False)) ∨ (((p2 ∧ p6) → (p5 ∨ p2)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_28 : (p2 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_11 := assump_4 assump_28
      apply False.elim assump_11
  case inr assump_3 =>
    have assump_29 : ((p2 ∧ p6) → (p5 ∨ p2)) := by
      intro assump_18
      cases assump_18
      case intro assump_19 assump_20 =>
        apply Or.inr
        exact assump_19
    let assump_17 := assump_3 assump_29
    apply False.elim assump_17


variable (p6 p5 p0 p2 : Prop)
theorem file82_81416 : ((((((p5 ∨ p2) ∨ (p0 → False)) → ((p0 ∧ False) → False)) → False) ∧ ((((p2 → False) → (p6 → False)) → ((p5 → p5) → (p5 → True))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : (((p2 → False) → (p6 → False)) → ((p5 → p5) → (p5 → True))) := by
      intro assump_9
      intro assump_10
      intro assump_11
      apply True.intro
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p3 p7 p6 p5 p2 p1 : Prop)
theorem file82_81942 : (((((p2 → False) → False) → ((True → p7) → False)) → (((p7 → p2) → False) ∧ ((p7 → False) ∨ (True → p6)))) → ((((p1 ∨ p5) → False) ∧ ((p6 → False) ∧ (p3 ∨ False))) → (((False ∨ p5) → (p3 ∨ p6)) ∨ ((True → p3) → (p2 → False))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      cases assump_8
      case inl assump_11 =>
        apply Or.inl
        intro assump_17
        cases assump_17
        case inl assump_18 =>
          apply False.elim assump_18
        case inr assump_19 =>
          apply Or.inl
          exact assump_11
      case inr assump_12 =>
        apply False.elim assump_12


variable (p6 p5 p7 p2 p1 : Prop)
theorem file82_82700 : ((((((True → False) ∧ (p5 ∧ p6)) → False) ∨ (((p7 ∧ p2) → (p1 ∨ False)) ∨ ((p5 → p5) → False))) → False) → False) := by
  intro assump_1
  have assump_25 : ((((True → False) ∧ (p5 ∧ p6)) → False) ∨ (((p7 ∧ p2) → (p1 ∨ False)) ∨ ((p5 → p5) → False))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        have assump_26 : True := by
          apply True.intro
        let assump_18 := assump_6 assump_26
        apply False.elim assump_18
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p2 p4 p0 p7 p3 p6 p1 : Prop)
theorem file82_83378 : ((((((p7 ∧ p0) → False) → ((p4 ∨ False) ∨ (p2 → False))) → (((p1 ∧ False) → False) ∨ ((p6 ∨ p3) ∧ (True → False)))) → False) → False) := by
  intro assump_31
  have assump_48 : ((((p7 ∧ p0) → False) → ((p4 ∨ False) ∨ (p2 → False))) → (((p1 ∧ False) → False) ∨ ((p6 ∨ p3) ∧ (True → False)))) := by
    intro assump_35
    apply Or.inl
    intro assump_38
    cases assump_38
    case intro assump_39 assump_40 =>
      apply False.elim assump_40
  let assump_34 := assump_31 assump_48
  apply False.elim assump_34


variable (p3 p5 p2 p1 p0 : Prop)
theorem file82_83948 : ((((((False ∨ p1) → (False → False)) → False) → (((p5 ∨ p3) → False) ∧ ((p0 ∧ p2) ∨ (True → False)))) → False) → False) := by
  intro assump_1
  have assump_49 : ((((False ∨ p1) → (False → False)) → False) → (((p5 ∨ p3) → False) ∧ ((p0 ∧ p2) ∨ (True → False)))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      have assump_50 : ((False ∨ p1) → (False → False)) := by
        intro assump_14
        intro assump_15
        apply False.elim assump_15
      let assump_13 := assump_5 assump_50
      apply False.elim assump_13
    case inr assump_8 =>
      have assump_51 : ((False ∨ p1) → (False → False)) := by
        intro assump_26
        intro assump_27
        apply False.elim assump_27
      let assump_25 := assump_5 assump_51
      apply False.elim assump_25
    apply Or.inr
    intro assump_35
    have assump_52 : ((False ∨ p1) → (False → False)) := by
      intro assump_39
      intro assump_40
      apply False.elim assump_40
    let assump_38 := assump_5 assump_52
    apply False.elim assump_38
  let assump_4 := assump_1 assump_49
  apply False.elim assump_4


variable (p1 p5 p4 p7 p0 p2 p3 p6 : Prop)
theorem file82_85159 : (((((p7 ∨ True) ∧ (p5 → p4)) → False) ∧ (((False ∧ p7) → (p3 → False)) ∧ ((p6 → False) ∧ (p4 ∨ p6)))) → ((((p0 ∨ p0) → (True → p1)) ∧ ((p5 → False) ∧ (p1 → p1))) ∨ (((p5 ∨ p2) ∨ (p4 ∧ p2)) → ((p5 → False) ∨ (p7 → False))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_11
        case inl assump_14 =>
          apply Or.inl
          apply And.intro
          intro assump_18
          intro assump_19
          cases assump_18
          case inl assump_22 =>
            have assump_103 : ((p7 ∨ True) ∧ (p5 → p4)) := by
              apply And.intro
              apply Or.inr
              apply True.intro
              intro assump_31
              exact assump_14
            let assump_30 := assump_2 assump_103
            apply False.elim assump_30
          case inr assump_23 =>
            have assump_104 : ((p7 ∨ True) ∧ (p5 → p4)) := by
              apply And.intro
              apply Or.inr
              apply True.intro
              intro assump_44
              exact assump_14
            let assump_43 := assump_2 assump_104
            apply False.elim assump_43
          apply And.intro
          intro assump_50
          have assump_105 : ((p7 ∨ True) ∧ (p5 → p4)) := by
            apply And.intro
            apply Or.inr
            apply True.intro
            intro assump_58
            exact assump_14
          let assump_57 := assump_2 assump_105
          apply False.elim assump_57
          intro assump_64
          exact assump_64
        case inr assump_15 =>
          apply Or.inl
          apply And.intro
          intro assump_69
          intro assump_70
          cases assump_69
          case inl assump_73 =>
            have assump_106 : p6 := by
              exact assump_15
            let assump_79 := assump_10 assump_106
            apply False.elim assump_79
          case inr assump_74 =>
            have assump_107 : p6 := by
              exact assump_15
            let assump_87 := assump_10 assump_107
            apply False.elim assump_87
          apply And.intro
          intro assump_91
          have assump_108 : p6 := by
            exact assump_15
          let assump_96 := assump_10 assump_108
          apply False.elim assump_96
          intro assump_100
          exact assump_100


variable (p2 p0 p7 p1 p4 p5 p3 p6 : Prop)
theorem file82_87659 : (((((p7 → p2) ∨ (p5 → p4)) ∧ ((p3 → False) ∧ (False ∧ p1))) → False) ∧ ((((p4 → True) ∨ (p2 ∨ False)) → ((p5 → p5) ∧ (p0 ∨ p0))) → (((p1 ∧ False) → False) ∨ ((p2 ∨ p6) ∧ (p5 → p4))))) := by
  apply And.intro
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          apply False.elim assump_12
    case inr assump_5 =>
      cases assump_3
      case intro assump_18 assump_19 =>
        cases assump_19
        case intro assump_22 assump_23 =>
          apply False.elim assump_22
  intro assump_26
  apply Or.inl
  intro assump_29
  cases assump_29
  case intro assump_30 assump_31 =>
    apply False.elim assump_31


variable (p3 p5 p2 p1 p7 : Prop)
theorem file82_88522 : (((((False → False) ∨ (p3 → p1)) → ((p3 → p2) → False)) ∧ (((p5 → p5) → False) ∧ ((p7 ∨ p5) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_20 : (p5 → p5) := by
        intro assump_14
        exact assump_14
      let assump_13 := assump_6 assump_20
      apply False.elim assump_13


variable (p7 p2 : Prop)
theorem file82_88973 : ((((((p2 → False) → False) ∧ ((p7 → False) ∧ (p2 → False))) → (((True → False) → (False → False)) ∨ ((p2 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_23 : ((((p2 → False) → False) ∧ ((p7 → False) ∧ (p2 → False))) → (((True → False) → (False → False)) ∨ ((p2 → False) → False))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        apply Or.inl
        intro assump_16
        intro assump_17
        apply False.elim assump_17
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p4 p5 p0 p6 p7 p1 p3 : Prop)
theorem file82_89654 : (((((p4 → p4) → False) → False) ∨ (((p6 ∧ p0) → False) ∨ ((p6 ∨ p1) ∨ (p4 ∨ False)))) ∨ ((((p5 ∨ False) → (p5 → p4)) ∧ ((p7 → False) ∨ (p3 → p5))) ∧ (((p3 → False) ∨ (p3 → False)) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  have assump_11 : (p4 → p4) := by
    intro assump_5
    exact assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p0 p3 p7 p4 p6 p2 p1 : Prop)
theorem file82_90099 : ((((((p6 ∨ False) ∧ (p7 → False)) ∨ ((False → False) ∨ (p2 → False))) ∨ (((True → False) ∨ (p7 ∧ p7)) → False)) ∧ ((((p6 ∧ p2) → (p1 → p3)) → ((False → False) → False)) ∧ (((False ∧ p0) ∧ (False → False)) ∨ ((p4 ∧ False) ∧ (p3 → False))))) → False) := by
  intro assump_12
  cases assump_12
  case intro assump_13 assump_14 =>
    cases assump_13
    case inl assump_15 =>
      cases assump_15
      case inl assump_17 =>
        cases assump_17
        case intro assump_19 assump_20 =>
          cases assump_19
          case inl assump_21 =>
            cases assump_14
            case intro assump_27 assump_28 =>
              cases assump_28
              case inl assump_31 =>
                cases assump_31
                case intro assump_33 assump_34 =>
                  cases assump_33
                  case intro assump_35 assump_36 =>
                    apply False.elim assump_35
              case inr assump_32 =>
                cases assump_32
                case intro assump_39 assump_40 =>
                  cases assump_39
                  case intro assump_41 assump_42 =>
                    apply False.elim assump_42
          case inr assump_22 =>
            apply False.elim assump_22
      case inr assump_18 =>
        cases assump_18
        case inl assump_49 =>
          cases assump_14
          case intro assump_53 assump_54 =>
            cases assump_54
            case inl assump_57 =>
              cases assump_57
              case intro assump_59 assump_60 =>
                cases assump_59
                case intro assump_61 assump_62 =>
                  apply False.elim assump_61
            case inr assump_58 =>
              cases assump_58
              case intro assump_65 assump_66 =>
                cases assump_65
                case intro assump_67 assump_68 =>
                  apply False.elim assump_68
        case inr assump_50 =>
          cases assump_14
          case intro assump_75 assump_76 =>
            cases assump_76
            case inl assump_79 =>
              cases assump_79
              case intro assump_81 assump_82 =>
                cases assump_81
                case intro assump_83 assump_84 =>
                  apply False.elim assump_83
            case inr assump_80 =>
              cases assump_80
              case intro assump_87 assump_88 =>
                cases assump_87
                case intro assump_89 assump_90 =>
                  apply False.elim assump_90
    case inr assump_16 =>
      cases assump_14
      case intro assump_97 assump_98 =>
        cases assump_98
        case inl assump_101 =>
          cases assump_101
          case intro assump_103 assump_104 =>
            cases assump_103
            case intro assump_105 assump_106 =>
              apply False.elim assump_105
        case inr assump_102 =>
          cases assump_102
          case intro assump_109 assump_110 =>
            cases assump_109
            case intro assump_111 assump_112 =>
              apply False.elim assump_112


variable (p4 p7 p2 : Prop)
theorem file82_93196 : ((((((p4 ∨ p7) → False) ∧ ((p2 ∧ p2) ∨ (True ∧ p2))) → (((True ∧ True) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_43 : ((((p4 ∨ p7) → False) ∧ ((p2 ∧ p2) ∨ (True ∧ p2))) → (((True ∧ True) → False) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_10
      case inl assump_13 =>
        cases assump_13
        case intro assump_15 assump_16 =>
          have assump_44 : (True ∧ True) := by
            apply And.intro
            apply True.intro
            apply True.intro
          let assump_24 := assump_6 assump_44
          apply False.elim assump_24
      case inr assump_14 =>
        cases assump_14
        case intro assump_28 assump_29 =>
          have assump_45 : (True ∧ True) := by
            apply And.intro
            apply True.intro
            apply True.intro
          let assump_36 := assump_6 assump_45
          apply False.elim assump_36
  let assump_4 := assump_1 assump_43
  apply False.elim assump_4


variable (p1 p5 p4 p7 p6 p3 p2 : Prop)
theorem file82_94304 : ((((((p7 ∨ False) → (p4 → False)) ∨ ((p6 ∨ False) ∨ (p4 ∧ p5))) → (((False ∧ True) ∧ (p6 → False)) → ((p7 ∧ p2) ∧ (p2 ∨ p1)))) ∧ ((((p6 ∧ p5) ∨ (p2 ∧ p5)) → ((p4 → p5) ∨ (p2 ∧ p3))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_33 : (((p6 ∧ p5) ∨ (p2 ∧ p5)) → ((p4 → p5) ∨ (p2 ∧ p3))) := by
      intro assump_9
      cases assump_9
      case inl assump_10 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          apply Or.inl
          intro assump_18
          exact assump_13
      case inr assump_11 =>
        cases assump_11
        case intro assump_21 assump_22 =>
          apply Or.inl
          intro assump_27
          exact assump_22
    let assump_8 := assump_3 assump_33
    apply False.elim assump_8


variable (p1 p5 p0 p4 p3 p7 p6 p2 : Prop)
theorem file82_95173 : (((((p1 → False) ∨ (p5 ∧ p4)) ∧ ((True → p6) ∨ (p5 ∧ True))) → (((p5 ∧ p4) → (p3 ∧ p5)) ∨ ((p6 → p3) → (p7 → False)))) → ((((False → False) ∨ (p0 ∧ p2)) ∨ ((True ∨ p3) ∧ (True ∨ p2))) ∨ (((p0 ∧ p5) ∧ (p7 ∧ p1)) ∨ ((False ∧ p3) → (p2 → p4))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_4
  apply False.elim assump_4


variable (p7 p1 p0 p6 p5 p3 : Prop)
theorem file82_95589 : ((((((p1 → p3) → False) ∧ ((True → p3) → False)) → False) ∧ ((((False → p5) ∨ (False → False)) → False) ∧ (((p0 ∧ p7) ∧ (False ∨ p0)) → ((False → False) ∧ (p0 ∧ p6))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_20 : ((False → p5) ∨ (False → False)) := by
        apply Or.inl
        intro assump_14
        apply False.elim assump_14
      let assump_13 := assump_6 assump_20
      apply False.elim assump_13


variable (p5 p4 p2 : Prop)
theorem file82_96164 : (((((p4 → p4) → False) → ((p2 → False) ∧ (p5 → p4))) → False) → False) := by
  intro assump_1
  have assump_33 : (((p4 → p4) → False) → ((p2 → False) ∧ (p5 → p4))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    have assump_34 : (p4 → p4) := by
      intro assump_12
      exact assump_12
    let assump_11 := assump_5 assump_34
    apply False.elim assump_11
    intro assump_18
    have assump_35 : (p4 → p4) := by
      intro assump_24
      exact assump_24
    let assump_23 := assump_5 assump_35
    apply False.elim assump_23
  let assump_4 := assump_1 assump_33
  apply False.elim assump_4


variable (p7 p6 p1 p3 p5 p2 p0 : Prop)
theorem file82_96844 : ((((((p2 ∨ p6) ∧ (True → False)) → False) → False) ∧ ((((p0 → False) ∨ (True → True)) ∨ ((p5 → False) ∧ (p7 → p2))) ∧ (((p0 ∨ p6) ∧ (p1 ∧ p3)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          have assump_111 : (((p2 ∨ p6) ∧ (True → False)) → False) := by
            intro assump_19
            cases assump_19
            case intro assump_20 assump_21 =>
              cases assump_20
              case inl assump_22 =>
                have assump_112 : True := by
                  apply True.intro
                let assump_28 := assump_21 assump_112
                apply False.elim assump_28
              case inr assump_23 =>
                have assump_113 : True := by
                  apply True.intro
                let assump_36 := assump_21 assump_113
                apply False.elim assump_36
          let assump_18 := assump_2 assump_111
          apply False.elim assump_18
        case inr assump_11 =>
          have assump_114 : (((p2 ∨ p6) ∧ (True → False)) → False) := by
            intro assump_51
            cases assump_51
            case intro assump_52 assump_53 =>
              cases assump_52
              case inl assump_54 =>
                have assump_115 : True := by
                  apply True.intro
                let assump_60 := assump_53 assump_115
                apply False.elim assump_60
              case inr assump_55 =>
                have assump_116 : True := by
                  apply True.intro
                let assump_68 := assump_53 assump_116
                apply False.elim assump_68
          let assump_50 := assump_2 assump_114
          apply False.elim assump_50
      case inr assump_9 =>
        cases assump_9
        case intro assump_75 assump_76 =>
          have assump_117 : (((p2 ∨ p6) ∧ (True → False)) → False) := by
            intro assump_87
            cases assump_87
            case intro assump_88 assump_89 =>
              cases assump_88
              case inl assump_90 =>
                have assump_118 : True := by
                  apply True.intro
                let assump_96 := assump_89 assump_118
                apply False.elim assump_96
              case inr assump_91 =>
                have assump_119 : True := by
                  apply True.intro
                let assump_104 := assump_89 assump_119
                apply False.elim assump_104
          let assump_86 := assump_2 assump_117
          apply False.elim assump_86


variable (p0 p4 p5 p1 p3 p6 : Prop)
theorem file82_99566 : ((((((False ∧ p0) → False) → False) ∧ (((p3 ∧ False) ∨ (p6 ∨ False)) → False)) ∧ ((((True ∨ p3) → False) → ((p5 ∨ p5) ∧ (p6 ∨ p0))) ∧ (((p0 ∧ p3) ∨ (p4 → p5)) ∧ ((True ∧ False) ∧ (p1 ∨ p3))))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_7
      case intro assump_14 assump_15 =>
        cases assump_15
        case intro assump_18 assump_19 =>
          cases assump_18
          case inl assump_20 =>
            cases assump_20
            case intro assump_22 assump_23 =>
              cases assump_19
              case intro assump_28 assump_29 =>
                cases assump_28
                case intro assump_30 assump_31 =>
                  apply False.elim assump_31
          case inr assump_21 =>
            cases assump_19
            case intro assump_38 assump_39 =>
              cases assump_38
              case intro assump_40 assump_41 =>
                apply False.elim assump_41


variable (p0 p5 p7 p1 p3 p4 : Prop)
theorem file82_100648 : ((((((p0 → p1) ∨ (p5 ∧ p4)) ∧ ((False ∧ p4) ∧ (p0 → False))) → (((p0 → False) → (p7 → p4)) ∧ ((p0 ∨ p3) → False))) → False) → False) := by
  intro assump_1
  have assump_94 : ((((p0 → p1) ∨ (p5 ∧ p4)) ∧ ((False ∧ p4) ∧ (p0 → False))) → (((p0 → False) → (p7 → p4)) ∧ ((p0 ∨ p3) → False))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    intro assump_7
    cases assump_5
    case intro assump_12 assump_13 =>
      cases assump_12
      case inl assump_14 =>
        cases assump_13
        case intro assump_18 assump_19 =>
          cases assump_18
          case intro assump_20 assump_21 =>
            apply False.elim assump_20
      case inr assump_15 =>
        cases assump_15
        case intro assump_24 assump_25 =>
          cases assump_13
          case intro assump_30 assump_31 =>
            cases assump_30
            case intro assump_32 assump_33 =>
              apply False.elim assump_32
    intro assump_36
    cases assump_36
    case inl assump_37 =>
      cases assump_5
      case intro assump_41 assump_42 =>
        cases assump_41
        case inl assump_43 =>
          cases assump_42
          case intro assump_47 assump_48 =>
            cases assump_47
            case intro assump_49 assump_50 =>
              apply False.elim assump_49
        case inr assump_44 =>
          cases assump_44
          case intro assump_53 assump_54 =>
            cases assump_42
            case intro assump_59 assump_60 =>
              cases assump_59
              case intro assump_61 assump_62 =>
                apply False.elim assump_61
    case inr assump_38 =>
      cases assump_5
      case intro assump_67 assump_68 =>
        cases assump_67
        case inl assump_69 =>
          cases assump_68
          case intro assump_73 assump_74 =>
            cases assump_73
            case intro assump_75 assump_76 =>
              apply False.elim assump_75
        case inr assump_70 =>
          cases assump_70
          case intro assump_79 assump_80 =>
            cases assump_68
            case intro assump_85 assump_86 =>
              cases assump_85
              case intro assump_87 assump_88 =>
                apply False.elim assump_87
  let assump_4 := assump_1 assump_94
  apply False.elim assump_4


variable (p7 p0 p5 p4 p3 : Prop)
theorem file82_102984 : ((((((p0 → False) → (True ∨ p4)) → False) → (((p4 → False) → (p7 ∨ p4)) ∨ ((p7 → p3) ∧ (True → False)))) ∧ ((((p4 ∨ p7) ∧ (False → False)) ∨ ((False → p5) ∨ (p5 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : (((p4 ∨ p7) ∧ (False → False)) ∨ ((False → p5) ∨ (p5 → False))) := by
      apply Or.inr
      apply Or.inl
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p0 p4 p5 p2 p3 p6 p7 p1 : Prop)
theorem file82_103566 : (((((p5 ∧ p2) ∨ (True → False)) ∧ ((p3 → p7) → (p6 ∧ p6))) → (((False → False) ∨ (p2 ∧ p5)) ∨ ((False ∨ p1) ∨ (p0 ∨ p3)))) ∨ ((((p3 ∨ p4) → False) ∧ ((p3 → p0) ∧ (p2 → False))) ∧ (((p7 ∨ p5) ∧ (p2 → False)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        apply Or.inl
        apply Or.inl
        intro assump_14
        apply False.elim assump_14
    case inr assump_5 =>
      apply Or.inl
      apply Or.inl
      intro assump_21
      apply False.elim assump_21


variable (p5 p2 p4 p3 p0 p7 p6 : Prop)
theorem file82_104258 : (((((p0 ∧ p5) → (p0 ∧ True)) → False) ∧ (((p3 ∨ p7) ∨ (p7 ∧ p2)) → ((p7 ∨ p2) → False))) → ((((True ∧ p2) ∨ (p2 → False)) → False) → (((p6 ∧ p6) → False) → ((p3 ∨ p4) → (p2 ∧ p2))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  apply And.intro
  cases assump_4
  case inl assump_5 =>
    cases assump_1
    case intro assump_13 assump_14 =>
      have assump_107 : ((p0 ∧ p5) → (p0 ∧ True)) := by
        intro assump_22
        apply And.intro
        cases assump_22
        case intro assump_23 assump_24 =>
          exact assump_23
        apply True.intro
      let assump_21 := assump_13 assump_107
      apply False.elim assump_21
  case inr assump_6 =>
    cases assump_1
    case intro assump_38 assump_39 =>
      have assump_108 : ((p0 ∧ p5) → (p0 ∧ True)) := by
        intro assump_46
        apply And.intro
        cases assump_46
        case intro assump_47 assump_48 =>
          exact assump_47
        apply True.intro
      let assump_45 := assump_38 assump_108
      apply False.elim assump_45
  cases assump_4
  case inl assump_56 =>
    cases assump_1
    case intro assump_64 assump_65 =>
      have assump_109 : ((p0 ∧ p5) → (p0 ∧ True)) := by
        intro assump_73
        apply And.intro
        cases assump_73
        case intro assump_74 assump_75 =>
          exact assump_74
        apply True.intro
      let assump_72 := assump_64 assump_109
      apply False.elim assump_72
  case inr assump_57 =>
    cases assump_1
    case intro assump_89 assump_90 =>
      have assump_110 : ((p0 ∧ p5) → (p0 ∧ True)) := by
        intro assump_97
        apply And.intro
        cases assump_97
        case intro assump_98 assump_99 =>
          exact assump_98
        apply True.intro
      let assump_96 := assump_89 assump_110
      apply False.elim assump_96


variable (p3 p1 p6 p5 p2 p0 p4 p7 : Prop)
theorem file82_106147 : (((((p2 → p4) → False) → ((p6 ∨ p5) → (p2 ∨ p7))) → (((p0 ∧ p6) → (False → p7)) → ((p3 ∨ p3) ∨ (p5 → p5)))) ∨ ((((p5 ∧ p3) ∧ (p0 ∧ True)) → False) → (((True ∧ p2) → (p0 → False)) ∨ ((p4 ∨ p1) ∨ (p0 ∨ p0))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply Or.inr
  intro assump_7
  exact assump_7


variable (p6 p5 p2 p3 p1 p7 p4 : Prop)
theorem file82_106522 : ((((((False → p6) ∨ (p2 → False)) ∧ ((p4 ∧ True) ∨ (p4 ∨ False))) ∨ (((p3 → False) ∧ (p7 ∨ p5)) → ((p1 ∧ p7) → (True ∨ True)))) → False) → False) := by
  intro assump_1
  have assump_29 : ((((False → p6) ∨ (p2 → False)) ∧ ((p4 ∧ True) ∨ (p4 ∨ False))) ∨ (((p3 → False) ∧ (p7 ∨ p5)) → ((p1 ∧ p7) → (True ∨ True)))) := by
    apply Or.inr
    intro assump_8
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      cases assump_8
      case intro assump_16 assump_17 =>
        cases assump_17
        case inl assump_20 =>
          apply Or.inl
          apply True.intro
        case inr assump_21 =>
          apply Or.inl
          apply True.intro
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p3 p6 p2 p0 p5 p4 : Prop)
theorem file82_107324 : (((((p4 → p4) ∧ (p3 ∧ p6)) ∧ ((p4 ∧ p6) ∧ (p0 → p5))) ∧ (((p0 → False) ∧ (p3 → False)) ∨ ((p2 → p2) → False))) → False) := by
  intro assump_16
  cases assump_16
  case intro assump_17 assump_18 =>
    cases assump_17
    case intro assump_19 assump_20 =>
      cases assump_19
      case intro assump_21 assump_22 =>
        cases assump_22
        case intro assump_25 assump_26 =>
          cases assump_20
          case intro assump_31 assump_32 =>
            cases assump_31
            case intro assump_33 assump_34 =>
              cases assump_18
              case inl assump_41 =>
                cases assump_41
                case intro assump_43 assump_44 =>
                  have assump_62 : p3 := by
                    exact assump_25
                  let assump_49 := assump_44 assump_62
                  apply False.elim assump_49
              case inr assump_42 =>
                have assump_63 : (p2 → p2) := by
                  intro assump_56
                  exact assump_56
                let assump_55 := assump_42 assump_63
                apply False.elim assump_55


variable (p6 p0 p7 p2 p4 p1 : Prop)
theorem file82_108489 : (((((False ∧ p1) → (True → p0)) ∧ ((p1 → p7) → (False → p4))) ∨ (((p1 ∧ p0) → (p4 → False)) ∨ ((p2 ∧ p2) ∨ (False → False)))) ∨ ((((p6 ∧ False) → False) ∨ ((p4 → p2) → (p4 → False))) ∨ (((p6 → p6) ∧ (p6 → False)) → ((p6 ∧ p6) ∧ (p4 ∧ True))))) := by
  apply Or.inl
  apply Or.inl
  apply And.intro
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    apply False.elim assump_5
  intro assump_9
  intro assump_10
  apply False.elim assump_10


variable (p2 p6 p4 p0 p5 p1 p3 : Prop)
theorem file82_109029 : (((((p1 → False) → False) → ((p5 → False) → (False → False))) → False) → ((((p6 ∧ p2) → (p4 → p0)) → ((p5 ∧ p3) ∧ (p5 → False))) → (((p2 ∧ p1) → (True → False)) → ((p0 → p5) ∨ (p3 → p2))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  apply Or.inl
  intro assump_10
  have assump_23 : (((p1 → False) → False) → ((p5 → False) → (False → False))) := by
    intro assump_15
    intro assump_16
    intro assump_17
    apply False.elim assump_17
  let assump_14 := assump_1 assump_23
  apply False.elim assump_14


variable (p6 p5 p4 p0 p3 : Prop)
theorem file82_109609 : (((((p6 → p4) ∧ (p4 ∧ False)) → False) → False) → ((((p5 ∨ p4) → (p3 → p5)) → ((p0 ∨ p0) ∧ (p3 → False))) → (((p0 ∨ p4) ∨ (p0 ∧ p4)) → ((False ∨ False) ∨ (p5 ∧ p5))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_4
    case inl assump_6 =>
      have assump_75 : (((p6 → p4) ∧ (p4 ∧ False)) → False) := by
        intro assump_15
        cases assump_15
        case intro assump_16 assump_17 =>
          cases assump_17
          case intro assump_20 assump_21 =>
            apply False.elim assump_21
      let assump_14 := assump_1 assump_75
      apply False.elim assump_14
    case inr assump_7 =>
      have assump_76 : (((p6 → p4) ∧ (p4 ∧ False)) → False) := by
        intro assump_36
        cases assump_36
        case intro assump_37 assump_38 =>
          cases assump_38
          case intro assump_41 assump_42 =>
            apply False.elim assump_42
      let assump_35 := assump_1 assump_76
      apply False.elim assump_35
  case inr assump_5 =>
    cases assump_5
    case intro assump_50 assump_51 =>
      have assump_77 : (((p6 → p4) ∧ (p4 ∧ False)) → False) := by
        intro assump_61
        cases assump_61
        case intro assump_62 assump_63 =>
          cases assump_63
          case intro assump_66 assump_67 =>
            apply False.elim assump_67
      let assump_60 := assump_1 assump_77
      apply False.elim assump_60


variable (p0 p1 p4 p3 p6 p2 p7 : Prop)
theorem file82_111106 : (((((True → p2) ∧ (p0 → False)) → False) → (((p0 → p0) ∧ (p1 ∨ p6)) → False)) → ((((p2 ∨ p7) ∧ (p4 ∨ p3)) → ((p1 → False) → False)) → (((p0 ∨ p3) → False) → ((p6 ∧ p6) → (p0 ∨ True))))) := by
  intro assump_14
  intro assump_15
  intro assump_16
  intro assump_17
  cases assump_17
  case intro assump_18 assump_19 =>
    apply Or.inr
    apply True.intro


variable (p3 p7 p4 p2 p1 : Prop)
theorem file82_111519 : ((((((p7 ∨ p1) → (p3 → p1)) → False) → (((p2 → False) → False) → ((p3 → True) ∨ (p4 ∧ False)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p7 ∨ p1) → (p3 → p1)) → False) → (((p2 → False) → False) → ((p3 → True) ∨ (p4 ∧ False)))) := by
    intro assump_5
    intro assump_6
    apply Or.inl
    intro assump_11
    apply True.intro
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p7 p2 p4 p0 p3 p1 p5 : Prop)
theorem file82_111999 : (((((True → p7) → False) ∧ ((False ∧ p1) ∨ (p3 ∨ p2))) → (((p7 ∧ p0) ∧ (p3 → False)) → False)) ∧ ((((p1 → p0) ∨ (True ∨ p0)) → ((p4 → False) → False)) → (((True ∧ True) ∨ (p4 → False)) ∨ ((p2 → p0) ∨ (True ∨ p5))))) := by
  apply And.intro
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_1
      case intro assump_13 assump_14 =>
        cases assump_14
        case inl assump_17 =>
          cases assump_17
          case intro assump_19 assump_20 =>
            apply False.elim assump_19
        case inr assump_18 =>
          cases assump_18
          case inl assump_23 =>
            have assump_48 : (True → p7) := by
              intro assump_29
              exact assump_5
            let assump_28 := assump_13 assump_48
            apply False.elim assump_28
          case inr assump_24 =>
            have assump_49 : (True → p7) := by
              intro assump_39
              exact assump_5
            let assump_38 := assump_13 assump_49
            apply False.elim assump_38
  intro assump_45
  apply Or.inl
  apply Or.inl
  apply And.intro
  apply True.intro
  apply True.intro


variable (p0 p7 p3 p1 p2 p4 p6 p5 : Prop)
theorem file82_113281 : (((((p2 ∧ True) → (p6 ∨ False)) ∧ ((p0 ∧ False) ∧ (p2 → False))) ∧ (((True ∧ p7) → (p1 → p1)) ∧ ((p2 ∨ p4) ∧ (p1 → False)))) → ((((p6 → p5) → (p0 ∧ p7)) ∨ ((True ∧ p0) → (p3 ∨ p6))) ∧ (((p3 ∧ True) → (p0 → p0)) ∧ ((p7 ∨ False) → (p7 → False))))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply False.elim assump_11
  apply And.intro
  intro assump_16
  intro assump_17
  cases assump_16
  case intro assump_20 assump_21 =>
    cases assump_1
    case intro assump_26 assump_27 =>
      cases assump_26
      case intro assump_28 assump_29 =>
        cases assump_29
        case intro assump_32 assump_33 =>
          cases assump_32
          case intro assump_34 assump_35 =>
            apply False.elim assump_35
  intro assump_40
  intro assump_41
  cases assump_40
  case inl assump_44 =>
    cases assump_1
    case intro assump_48 assump_49 =>
      cases assump_48
      case intro assump_50 assump_51 =>
        cases assump_51
        case intro assump_54 assump_55 =>
          cases assump_54
          case intro assump_56 assump_57 =>
            apply False.elim assump_57
  case inr assump_45 =>
    apply False.elim assump_45


variable (p4 p3 p0 p7 p6 p1 : Prop)
theorem file82_114724 : ((((((False ∨ p3) ∨ (p7 → p4)) → False) → (((p6 ∨ p4) ∨ (p0 ∨ p0)) → False)) ∧ ((((p7 ∨ p1) → False) → ((p4 ∧ p3) → (True → True))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : (((p7 ∨ p1) → False) → ((p4 ∧ p3) → (True → True))) := by
      intro assump_9
      intro assump_10
      intro assump_11
      apply True.intro
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p1 p3 p6 p2 p7 p4 : Prop)
theorem file82_115245 : (((((True ∧ True) ∧ (False → p4)) → False) ∧ (((p2 → False) ∨ (p2 ∧ p1)) ∧ ((p2 → p1) ∨ (p1 ∨ True)))) → ((((p3 ∧ p4) → False) ∨ ((p2 → False) ∨ (p6 ∨ True))) ∧ (((p7 ∧ p6) → False) → False))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case inl assump_12 =>
          apply Or.inl
          intro assump_16
          cases assump_16
          case intro assump_17 assump_18 =>
            have assump_243 : ((True ∧ True) ∧ (False → p4)) := by
              apply And.intro
              apply And.intro
              apply True.intro
              apply True.intro
              intro assump_28
              apply False.elim assump_28
            let assump_27 := assump_2 assump_243
            apply False.elim assump_27
        case inr assump_13 =>
          cases assump_13
          case inl assump_34 =>
            apply Or.inl
            intro assump_38
            cases assump_38
            case intro assump_39 assump_40 =>
              have assump_244 : ((True ∧ True) ∧ (False → p4)) := by
                apply And.intro
                apply And.intro
                apply True.intro
                apply True.intro
                intro assump_50
                apply False.elim assump_50
              let assump_49 := assump_2 assump_244
              apply False.elim assump_49
          case inr assump_35 =>
            apply Or.inl
            intro assump_58
            cases assump_58
            case intro assump_59 assump_60 =>
              have assump_245 : ((True ∧ True) ∧ (False → p4)) := by
                apply And.intro
                apply And.intro
                apply True.intro
                apply True.intro
                intro assump_69
                apply False.elim assump_69
              let assump_68 := assump_2 assump_245
              apply False.elim assump_68
      case inr assump_9 =>
        cases assump_9
        case intro assump_75 assump_76 =>
          cases assump_7
          case inl assump_81 =>
            apply Or.inl
            intro assump_85
            cases assump_85
            case intro assump_86 assump_87 =>
              have assump_246 : ((True ∧ True) ∧ (False → p4)) := by
                apply And.intro
                apply And.intro
                apply True.intro
                apply True.intro
                intro assump_99
                apply False.elim assump_99
              let assump_98 := assump_2 assump_246
              apply False.elim assump_98
          case inr assump_82 =>
            cases assump_82
            case inl assump_105 =>
              apply Or.inl
              intro assump_109
              cases assump_109
              case intro assump_110 assump_111 =>
                have assump_247 : ((True ∧ True) ∧ (False → p4)) := by
                  apply And.intro
                  apply And.intro
                  apply True.intro
                  apply True.intro
                  intro assump_122
                  apply False.elim assump_122
                let assump_121 := assump_2 assump_247
                apply False.elim assump_121
            case inr assump_106 =>
              apply Or.inl
              intro assump_130
              cases assump_130
              case intro assump_131 assump_132 =>
                have assump_248 : ((True ∧ True) ∧ (False → p4)) := by
                  apply And.intro
                  apply And.intro
                  apply True.intro
                  apply True.intro
                  intro assump_142
                  apply False.elim assump_142
                let assump_141 := assump_2 assump_248
                apply False.elim assump_141
  intro assump_148
  cases assump_1
  case intro assump_151 assump_152 =>
    cases assump_152
    case intro assump_155 assump_156 =>
      cases assump_155
      case inl assump_157 =>
        cases assump_156
        case inl assump_161 =>
          have assump_249 : ((True ∧ True) ∧ (False → p4)) := by
            apply And.intro
            apply And.intro
            apply True.intro
            apply True.intro
            intro assump_168
            apply False.elim assump_168
          let assump_167 := assump_151 assump_249
          apply False.elim assump_167
        case inr assump_162 =>
          cases assump_162
          case inl assump_174 =>
            have assump_250 : ((True ∧ True) ∧ (False → p4)) := by
              apply And.intro
              apply And.intro
              apply True.intro
              apply True.intro
              intro assump_181
              apply False.elim assump_181
            let assump_180 := assump_151 assump_250
            apply False.elim assump_180
          case inr assump_175 =>
            have assump_251 : ((True ∧ True) ∧ (False → p4)) := by
              apply And.intro
              apply And.intro
              apply True.intro
              apply True.intro
              intro assump_191
              apply False.elim assump_191
            let assump_190 := assump_151 assump_251
            apply False.elim assump_190
      case inr assump_158 =>
        cases assump_158
        case intro assump_197 assump_198 =>
          cases assump_156
          case inl assump_203 =>
            have assump_252 : ((True ∧ True) ∧ (False → p4)) := by
              apply And.intro
              apply And.intro
              apply True.intro
              apply True.intro
              intro assump_212
              apply False.elim assump_212
            let assump_211 := assump_151 assump_252
            apply False.elim assump_211
          case inr assump_204 =>
            cases assump_204
            case inl assump_218 =>
              have assump_253 : ((True ∧ True) ∧ (False → p4)) := by
                apply And.intro
                apply And.intro
                apply True.intro
                apply True.intro
                intro assump_226
                apply False.elim assump_226
              let assump_225 := assump_151 assump_253
              apply False.elim assump_225
            case inr assump_219 =>
              have assump_254 : ((True ∧ True) ∧ (False → p4)) := by
                apply And.intro
                apply And.intro
                apply True.intro
                apply True.intro
                intro assump_237
                apply False.elim assump_237
              let assump_236 := assump_151 assump_254
              apply False.elim assump_236


variable (p0 p7 p1 p2 p4 p6 p5 : Prop)
theorem file82_121947 : (((((p5 ∧ p4) ∧ (False ∧ p1)) → False) ∧ (((False → p5) ∨ (p6 → False)) → ((p1 → p2) ∨ (p5 → False)))) → ((((p0 → p7) → (p6 → p6)) ∨ ((p5 → False) → False)) ∨ (((p7 → False) ∧ (p0 ∧ True)) ∨ ((p7 ∨ p6) ∧ (False → p0))))) := by
  intro assump_13
  cases assump_13
  case intro assump_14 assump_15 =>
    apply Or.inl
    apply Or.inl
    intro assump_20
    intro assump_21
    exact assump_21


variable (p7 p4 p1 p3 : Prop)
theorem file82_122394 : ((((((p3 → p3) ∨ (p7 → True)) ∧ ((p4 ∧ p1) ∧ (False ∧ p7))) → (((p4 ∧ p4) → (p3 → False)) → False)) → False) → False) := by
  intro assump_1
  have assump_44 : ((((p3 → p3) ∨ (p7 → True)) ∧ ((p4 ∧ p1) ∧ (False ∧ p7))) → (((p4 ∧ p4) → (p3 → False)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        cases assump_10
        case intro assump_15 assump_16 =>
          cases assump_15
          case intro assump_17 assump_18 =>
            cases assump_16
            case intro assump_23 assump_24 =>
              apply False.elim assump_23
      case inr assump_12 =>
        cases assump_10
        case intro assump_29 assump_30 =>
          cases assump_29
          case intro assump_31 assump_32 =>
            cases assump_30
            case intro assump_37 assump_38 =>
              apply False.elim assump_37
  let assump_4 := assump_1 assump_44
  apply False.elim assump_4


