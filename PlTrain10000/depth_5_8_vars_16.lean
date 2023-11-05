variable (p7 p3 p4 p1 p2 : Prop)
theorem file16_41 : (((((True → False) ∨ (p1 → False)) ∧ ((p2 ∨ p4) → False)) ∧ (((p7 ∧ False) → (p3 → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        have assump_48 : ((p7 ∧ False) → (p3 → False)) := by
          intro assump_15
          intro assump_16
          cases assump_15
          case intro assump_19 assump_20 =>
            apply False.elim assump_20
        let assump_14 := assump_3 assump_48
        apply False.elim assump_14
      case inr assump_7 =>
        have assump_49 : ((p7 ∧ False) → (p3 → False)) := by
          intro assump_35
          intro assump_36
          cases assump_35
          case intro assump_39 assump_40 =>
            apply False.elim assump_40
        let assump_34 := assump_3 assump_49
        apply False.elim assump_34


variable (p3 p6 p4 p0 p7 p2 : Prop)
theorem file16_1017 : ((((((True → False) → (True ∧ p7)) ∧ ((False → False) ∧ (p6 → False))) ∧ (((p4 ∧ p0) ∧ (p7 ∨ False)) ∧ ((p0 ∨ p3) → False))) ∧ ((((p0 → p0) ∨ (p2 ∨ p0)) ∧ ((True ∧ p6) → (p7 ∧ p7))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          cases assump_5
          case intro assump_16 assump_17 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              cases assump_18
              case intro assump_20 assump_21 =>
                cases assump_19
                case inl assump_26 =>
                  have assump_56 : (((p0 → p0) ∨ (p2 ∨ p0)) ∧ ((True ∧ p6) → (p7 ∧ p7))) := by
                    apply And.intro
                    apply Or.inl
                    intro assump_35
                    exact assump_35
                    intro assump_38
                    apply And.intro
                    cases assump_38
                    case intro assump_39 assump_40 =>
                      exact assump_26
                    cases assump_38
                    case intro assump_45 assump_46 =>
                      exact assump_26
                  let assump_34 := assump_3 assump_56
                  apply False.elim assump_34
                case inr assump_27 =>
                  apply False.elim assump_27


variable (p4 p6 p2 p5 p1 p0 p7 : Prop)
theorem file16_2571 : ((((((p5 ∨ p0) → False) → ((p5 → p1) ∧ (p7 ∧ p2))) → (((p4 → False) → False) ∧ ((p4 ∧ p6) ∧ (False ∨ p7)))) ∧ ((((p6 ∨ p2) → False) → False) ∧ (((p7 → p1) ∨ (True → p2)) ∧ ((False → False) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          have assump_36 : (False → False) := by
            intro assump_19
            apply False.elim assump_19
          let assump_18 := assump_11 assump_36
          apply False.elim assump_18
        case inr assump_13 =>
          have assump_37 : (False → False) := by
            intro assump_30
            apply False.elim assump_30
          let assump_29 := assump_11 assump_37
          apply False.elim assump_29


variable (p4 p3 p5 p7 p6 p1 : Prop)
theorem file16_3515 : (((((False → False) ∨ (False → p7)) ∧ ((p3 → p4) → (p6 ∨ True))) → False) → ((((p7 → False) ∧ (p5 → p7)) ∨ ((p7 → False) → (p1 → p7))) → (((p7 ∨ p3) → False) → False))) := by
  intro assump_5
  intro assump_6
  intro assump_7
  cases assump_6
  case inl assump_10 =>
    cases assump_10
    case intro assump_12 assump_13 =>
      have assump_44 : (((False → False) ∨ (False → p7)) ∧ ((p3 → p4) → (p6 ∨ True))) := by
        apply And.intro
        apply Or.inl
        intro assump_21
        apply False.elim assump_21
        intro assump_24
        apply Or.inr
        apply True.intro
      let assump_20 := assump_5 assump_44
      apply False.elim assump_20
  case inr assump_11 =>
    have assump_45 : (((False → False) ∨ (False → p7)) ∧ ((p3 → p4) → (p6 ∨ True))) := by
      apply And.intro
      apply Or.inl
      intro assump_35
      apply False.elim assump_35
      intro assump_38
      apply Or.inr
      apply True.intro
    let assump_34 := assump_5 assump_45
    apply False.elim assump_34


variable (p1 p4 p2 p7 p0 : Prop)
theorem file16_4583 : ((((((p7 ∨ p1) → (p7 ∧ p7)) → False) ∧ (((p1 → False) → False) ∧ ((p7 → p7) → False))) ∨ ((((p2 ∧ False) ∧ (p0 → False)) → False) ∧ (((p2 ∧ p2) ∧ (False ∧ False)) ∧ ((p0 → False) ∧ (p4 → False))))) → False) := by
  intro assump_29
  cases assump_29
  case inl assump_30 =>
    cases assump_30
    case intro assump_32 assump_33 =>
      cases assump_33
      case intro assump_36 assump_37 =>
        have assump_67 : (p7 → p7) := by
          intro assump_43
          exact assump_43
        let assump_42 := assump_37 assump_67
        apply False.elim assump_42
  case inr assump_31 =>
    cases assump_31
    case intro assump_49 assump_50 =>
      cases assump_50
      case intro assump_53 assump_54 =>
        cases assump_53
        case intro assump_55 assump_56 =>
          cases assump_55
          case intro assump_57 assump_58 =>
            cases assump_56
            case intro assump_63 assump_64 =>
              apply False.elim assump_63


variable (p5 p0 p1 p7 p6 p4 p3 : Prop)
theorem file16_5607 : (((((p6 ∨ True) → False) ∧ ((p6 → False) ∧ (p0 → p1))) ∧ (((False ∨ p5) ∧ (p7 ∧ p4)) → False)) → ((((p1 ∧ True) ∨ (p3 → p1)) → ((p6 ∨ p7) → False)) ∨ (((p1 ∧ True) ∧ (p3 → False)) → ((p7 → False) → (p5 → False))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        apply Or.inl
        intro assump_16
        intro assump_17
        cases assump_17
        case inl assump_18 =>
          cases assump_16
          case inl assump_22 =>
            cases assump_22
            case intro assump_24 assump_25 =>
              have assump_78 : p6 := by
                exact assump_18
              let assump_34 := assump_8 assump_78
              apply False.elim assump_34
          case inr assump_23 =>
            have assump_79 : p6 := by
              exact assump_18
            let assump_44 := assump_8 assump_79
            apply False.elim assump_44
        case inr assump_19 =>
          cases assump_16
          case inl assump_50 =>
            cases assump_50
            case intro assump_52 assump_53 =>
              have assump_80 : (p6 ∨ True) := by
                apply Or.inr
                apply True.intro
              let assump_63 := assump_4 assump_80
              apply False.elim assump_63
          case inr assump_51 =>
            have assump_81 : (p6 ∨ True) := by
              apply Or.inr
              apply True.intro
            let assump_74 := assump_4 assump_81
            apply False.elim assump_74


variable (p6 p7 p3 p0 p1 p5 : Prop)
theorem file16_7263 : (((((p7 ∧ False) ∧ (p5 → p3)) → False) → False) → ((((p5 → p1) → (p3 ∧ p1)) ∨ ((p6 ∨ p3) → False)) ∧ (((p0 ∨ p6) ∧ (True ∨ False)) → ((p0 → False) ∨ (p3 ∧ p3))))) := by
  intro assump_12
  apply And.intro
  apply Or.inl
  intro assump_15
  apply And.intro
  have assump_107 : (((p7 ∧ False) ∧ (p5 → p3)) → False) := by
    intro assump_20
    cases assump_20
    case intro assump_21 assump_22 =>
      cases assump_21
      case intro assump_23 assump_24 =>
        apply False.elim assump_24
  let assump_19 := assump_12 assump_107
  apply False.elim assump_19
  have assump_108 : (((p7 ∧ False) ∧ (p5 → p3)) → False) := by
    intro assump_36
    cases assump_36
    case intro assump_37 assump_38 =>
      cases assump_37
      case intro assump_39 assump_40 =>
        apply False.elim assump_40
  let assump_35 := assump_12 assump_108
  apply False.elim assump_35
  intro assump_48
  cases assump_48
  case intro assump_49 assump_50 =>
    cases assump_49
    case inl assump_51 =>
      cases assump_50
      case inl assump_55 =>
        apply Or.inl
        intro assump_61
        have assump_109 : (((p7 ∧ False) ∧ (p5 → p3)) → False) := by
          intro assump_66
          cases assump_66
          case intro assump_67 assump_68 =>
            cases assump_67
            case intro assump_69 assump_70 =>
              apply False.elim assump_70
        let assump_65 := assump_12 assump_109
        apply False.elim assump_65
      case inr assump_56 =>
        apply False.elim assump_56
    case inr assump_52 =>
      cases assump_50
      case inl assump_82 =>
        apply Or.inl
        intro assump_88
        have assump_110 : (((p7 ∧ False) ∧ (p5 → p3)) → False) := by
          intro assump_93
          cases assump_93
          case intro assump_94 assump_95 =>
            cases assump_94
            case intro assump_96 assump_97 =>
              apply False.elim assump_97
        let assump_92 := assump_12 assump_110
        apply False.elim assump_92
      case inr assump_83 =>
        apply False.elim assump_83


variable (p5 p1 p2 p6 p7 p0 p3 : Prop)
theorem file16_9378 : (((((p0 ∨ p5) → False) ∧ ((True → False) ∧ (p7 → p1))) ∨ (((p2 → p6) ∧ (p3 → False)) → ((p6 ∨ p2) ∧ (p3 → p1)))) → ((((p1 → p1) ∧ (False ∨ p2)) → ((p3 → p2) ∨ (p2 ∨ True))) ∨ (((p5 → p0) → False) ∨ ((p6 ∧ p1) ∨ (p3 ∧ False))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        apply Or.inl
        intro assump_14
        cases assump_14
        case intro assump_15 assump_16 =>
          cases assump_16
          case inl assump_19 =>
            apply False.elim assump_19
          case inr assump_20 =>
            apply Or.inl
            intro assump_25
            exact assump_20
  case inr assump_3 =>
    apply Or.inl
    intro assump_30
    cases assump_30
    case intro assump_31 assump_32 =>
      cases assump_32
      case inl assump_35 =>
        apply False.elim assump_35
      case inr assump_36 =>
        apply Or.inl
        intro assump_41
        exact assump_36


variable (p4 p7 p5 p0 : Prop)
theorem file16_10458 : (((((p4 → p7) ∧ (False ∧ p4)) ∨ ((p0 ∨ p4) ∧ (False ∧ p4))) ∧ (((p0 ∧ True) ∨ (p0 ∨ p5)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          apply False.elim assump_10
    case inr assump_5 =>
      cases assump_5
      case intro assump_14 assump_15 =>
        cases assump_14
        case inl assump_16 =>
          cases assump_15
          case intro assump_20 assump_21 =>
            apply False.elim assump_20
        case inr assump_17 =>
          cases assump_15
          case intro assump_26 assump_27 =>
            apply False.elim assump_26


variable (p2 p6 p3 p0 p7 p4 p1 p5 : Prop)
theorem file16_11299 : (((((p4 → p7) ∧ (p0 → False)) ∧ ((False ∧ False) ∧ (p7 → p1))) → (((p1 → False) ∨ (p4 → p2)) ∧ ((p7 → p6) ∧ (p4 ∧ p2)))) ∨ ((((p5 ∧ p6) → (p5 → p3)) ∨ ((p0 → False) ∧ (p3 → False))) → False)) := by
  apply Or.inl
  intro assump_13
  apply And.intro
  cases assump_13
  case intro assump_14 assump_15 =>
    cases assump_14
    case intro assump_16 assump_17 =>
      cases assump_15
      case intro assump_22 assump_23 =>
        cases assump_22
        case intro assump_24 assump_25 =>
          apply False.elim assump_24
  apply And.intro
  intro assump_28
  cases assump_13
  case intro assump_31 assump_32 =>
    cases assump_31
    case intro assump_33 assump_34 =>
      cases assump_32
      case intro assump_39 assump_40 =>
        cases assump_39
        case intro assump_41 assump_42 =>
          apply False.elim assump_41
  apply And.intro
  cases assump_13
  case intro assump_45 assump_46 =>
    cases assump_45
    case intro assump_47 assump_48 =>
      cases assump_46
      case intro assump_53 assump_54 =>
        cases assump_53
        case intro assump_55 assump_56 =>
          apply False.elim assump_55
  cases assump_13
  case intro assump_59 assump_60 =>
    cases assump_59
    case intro assump_61 assump_62 =>
      cases assump_60
      case intro assump_67 assump_68 =>
        cases assump_67
        case intro assump_69 assump_70 =>
          apply False.elim assump_69


variable (p7 p3 p0 p1 p6 p4 p2 : Prop)
theorem file16_12773 : (((((p4 → p4) → (p4 → False)) ∧ ((p0 → False) ∧ (p4 ∨ False))) → False) ∨ ((((p2 → False) ∨ (p1 ∨ p6)) → False) → (((True → False) → (p3 → False)) ∧ ((p7 ∧ p4) → False)))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        have assump_26 : (p4 → p4) := by
          intro assump_17
          exact assump_17
        let assump_16 := assump_2 assump_26
        have assump_27 : p4 := by
          exact assump_10
        let assump_20 := assump_16 assump_27
        apply False.elim assump_20
      case inr assump_11 =>
        apply False.elim assump_11


variable (p4 p0 p3 : Prop)
theorem file16_13529 : ((((((False ∧ True) → (p3 → p0)) → False) → (((p4 → False) → False) ∨ ((False ∧ p3) → False))) → False) → False) := by
  intro assump_1
  have assump_27 : ((((False ∧ True) → (p3 → p0)) → False) → (((p4 → False) → False) ∨ ((False ∧ p3) → False))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    have assump_28 : ((False ∧ True) → (p3 → p0)) := by
      intro assump_13
      intro assump_14
      cases assump_13
      case intro assump_17 assump_18 =>
        apply False.elim assump_17
    let assump_12 := assump_5 assump_28
    apply False.elim assump_12
  let assump_4 := assump_1 assump_27
  apply False.elim assump_4


variable (p5 : Prop)
theorem file16_14216 : (((((True → False) ∧ (p5 → p5)) → False) → False) → False) := by
  intro assump_1
  have assump_20 : (((True → False) ∧ (p5 → p5)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_21 : True := by
        apply True.intro
      let assump_13 := assump_6 assump_21
      apply False.elim assump_13
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p7 p5 p1 p4 p3 p2 : Prop)
theorem file16_14695 : ((((((True ∨ p1) → (p2 → False)) ∨ ((p7 → p3) ∨ (p5 → p4))) → False) ∧ ((((True ∧ True) → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : (((True ∧ True) → False) → False) := by
      intro assump_9
      have assump_20 : (True ∧ True) := by
        apply And.intro
        apply True.intro
        apply True.intro
      let assump_12 := assump_9 assump_20
      apply False.elim assump_12
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


variable (p3 p7 p0 p1 p2 p5 p4 p6 : Prop)
theorem file16_15303 : (((((False ∧ p6) ∧ (p1 ∧ p4)) → False) ∨ (((p5 → False) → False) ∧ ((p5 → False) → False))) ∨ ((((p5 ∧ p3) ∨ (True → p0)) ∧ ((p4 ∨ p6) ∧ (p1 ∧ p1))) ∨ (((p3 ∧ p4) ∨ (p7 ∧ False)) → ((p6 ∧ p7) ∧ (p2 ∧ p5))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply False.elim assump_4


variable (p1 p4 p0 p2 p3 p5 p7 p6 : Prop)
theorem file16_15768 : (((((p2 → p4) ∨ (p6 → p2)) ∨ ((p4 → p1) → (p4 → p6))) ∨ (((False ∧ p2) ∧ (p2 → p2)) ∨ ((p3 ∧ p3) → False))) → ((((p2 → False) ∧ (p5 → False)) → ((False → False) ∨ (p6 ∨ p6))) ∨ (((p1 ∨ p7) ∨ (p0 ∨ p2)) → ((True → False) → (p1 ∧ p0))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        apply Or.inl
        intro assump_10
        cases assump_10
        case intro assump_11 assump_12 =>
          apply Or.inl
          intro assump_17
          apply False.elim assump_17
      case inr assump_7 =>
        apply Or.inl
        intro assump_22
        cases assump_22
        case intro assump_23 assump_24 =>
          apply Or.inl
          intro assump_29
          apply False.elim assump_29
    case inr assump_5 =>
      apply Or.inl
      intro assump_34
      cases assump_34
      case intro assump_35 assump_36 =>
        apply Or.inl
        intro assump_41
        apply False.elim assump_41
  case inr assump_3 =>
    cases assump_3
    case inl assump_44 =>
      cases assump_44
      case intro assump_46 assump_47 =>
        cases assump_46
        case intro assump_48 assump_49 =>
          apply False.elim assump_48
    case inr assump_45 =>
      apply Or.inl
      intro assump_54
      cases assump_54
      case intro assump_55 assump_56 =>
        apply Or.inl
        intro assump_61
        apply False.elim assump_61


variable (p7 p4 p1 p2 p6 p5 : Prop)
theorem file16_17290 : (((((p2 → False) ∧ (p1 ∧ True)) → ((True → False) → (p7 ∧ p4))) ∨ (((p1 → False) → (p5 ∨ p6)) → False)) ∨ ((((p6 ∧ p6) → False) ∧ ((p6 ∧ p2) → False)) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      have assump_39 : True := by
        apply True.intro
      let assump_17 := assump_2 assump_39
      apply False.elim assump_17
  cases assump_1
  case intro assump_23 assump_24 =>
    cases assump_24
    case intro assump_27 assump_28 =>
      have assump_40 : True := by
        apply True.intro
      let assump_35 := assump_2 assump_40
      apply False.elim assump_35


variable (p5 p6 p4 p1 p0 : Prop)
theorem file16_18082 : ((((((p0 ∧ p1) ∧ (p1 → False)) → False) ∨ (((p6 → False) ∨ (p4 ∨ p1)) ∨ ((False ∧ p1) → (p5 ∨ False)))) → False) → False) := by
  intro assump_7
  have assump_29 : ((((p0 ∧ p1) ∧ (p1 → False)) → False) ∨ (((p6 → False) ∨ (p4 ∨ p1)) ∨ ((False ∧ p1) → (p5 ∨ False)))) := by
    apply Or.inl
    intro assump_11
    cases assump_11
    case intro assump_12 assump_13 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        have assump_30 : p1 := by
          exact assump_15
        let assump_22 := assump_13 assump_30
        apply False.elim assump_22
  let assump_10 := assump_7 assump_29
  apply False.elim assump_10


variable (p6 p7 p3 p4 p1 p5 p2 p0 : Prop)
theorem file16_18784 : (((((p7 ∨ p4) ∨ (p1 ∧ p6)) → False) → (((p0 → p4) ∧ (p5 ∨ True)) → ((p2 → p2) ∨ (p5 → p4)))) ∨ ((((p3 → False) → (p0 → p5)) ∨ ((p2 → False) ∧ (p7 → False))) ∨ (((p6 → p2) ∨ (True → p4)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case inl assump_7 =>
      apply Or.inl
      intro assump_13
      exact assump_13
    case inr assump_8 =>
      apply Or.inl
      intro assump_20
      exact assump_20


variable (p5 p4 p3 : Prop)
theorem file16_19333 : ((((((p3 ∨ True) → False) → ((p3 → False) → (p4 → False))) ∨ (((p5 → p3) ∨ (True → False)) ∨ ((True → True) → (True → True)))) → False) → False) := by
  intro assump_1
  have assump_21 : ((((p3 ∨ True) → False) → ((p3 → False) → (p4 → False))) ∨ (((p5 → p3) ∨ (True → False)) ∨ ((True → True) → (True → True)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    have assump_22 : (p3 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_14 := assump_5 assump_22
    apply False.elim assump_14
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p0 p1 p7 p5 p3 p4 p2 : Prop)
theorem file16_20005 : (((((p1 → p7) → False) ∨ ((True ∨ p2) → (p0 ∨ True))) ∨ (((False ∧ p5) ∧ (p0 ∨ p3)) ∨ ((p3 ∧ p0) ∨ (p4 ∧ p0)))) → ((((False ∧ True) ∧ (True → False)) ∧ ((p3 → p5) → (p3 → True))) ∨ (((p0 ∨ False) → False) → ((p1 → True) ∨ (True → False))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      apply Or.inr
      intro assump_8
      apply Or.inl
      intro assump_11
      apply True.intro
    case inr assump_5 =>
      apply Or.inr
      intro assump_14
      apply Or.inl
      intro assump_17
      apply True.intro
  case inr assump_3 =>
    cases assump_3
    case inl assump_18 =>
      cases assump_18
      case intro assump_20 assump_21 =>
        cases assump_20
        case intro assump_22 assump_23 =>
          apply False.elim assump_22
    case inr assump_19 =>
      cases assump_19
      case inl assump_26 =>
        cases assump_26
        case intro assump_28 assump_29 =>
          apply Or.inr
          intro assump_34
          apply Or.inl
          intro assump_37
          apply True.intro
      case inr assump_27 =>
        cases assump_27
        case intro assump_38 assump_39 =>
          apply Or.inr
          intro assump_44
          apply Or.inl
          intro assump_47
          apply True.intro


variable (p3 p6 p5 p0 p2 p1 p4 p7 : Prop)
theorem file16_21372 : (((((True → False) → False) ∨ ((p6 ∨ p1) ∨ (p1 ∧ p7))) ∨ (((p0 → p0) ∨ (True ∧ p6)) ∨ ((p4 ∨ False) ∧ (p2 ∨ p7)))) ∨ ((((p5 ∨ p0) ∧ (p2 → False)) ∧ ((p5 ∨ p1) ∧ (p3 → False))) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  have assump_8 : True := by
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p0 p1 p7 p2 p5 p3 : Prop)
theorem file16_21800 : (((((p0 → p1) → (p1 ∨ p3)) ∨ ((p5 ∧ p1) ∧ (p5 ∨ p0))) → (((p1 ∧ p2) ∨ (p7 ∨ p5)) → False)) → ((((p3 → False) → False) → ((p0 ∧ False) → False)) ∨ (((p2 ∨ True) → False) → False))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    apply False.elim assump_7


variable (p0 p2 p5 p4 p1 p6 : Prop)
theorem file16_22193 : (((((False ∨ p2) → False) → False) → (((False → False) ∨ (p1 → p4)) → ((p2 ∨ p4) → (False → True)))) ∨ ((((p1 → p2) ∧ (p0 ∧ False)) ∧ ((p4 → False) ∧ (p4 → False))) → (((p6 → p0) ∨ (p0 ∧ p5)) ∨ ((p4 → False) ∨ (p0 → False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  apply True.intro


variable (p1 p4 p5 p3 p2 p7 p0 p6 : Prop)
theorem file16_22594 : (((((p1 → p4) → False) → ((p2 → p3) ∧ (p3 ∧ p3))) ∧ (((p5 ∧ p5) ∧ (p7 ∨ p1)) → False)) → ((((False → p6) → False) → ((p2 ∨ p5) → False)) ∨ (((True ∨ p4) → False) → ((p0 ∨ p0) ∨ (p6 → True))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    intro assump_8
    intro assump_9
    cases assump_9
    case inl assump_10 =>
      have assump_34 : (False → p6) := by
        intro assump_17
        apply False.elim assump_17
      let assump_16 := assump_8 assump_34
      apply False.elim assump_16
    case inr assump_11 =>
      have assump_35 : (False → p6) := by
        intro assump_28
        apply False.elim assump_28
      let assump_27 := assump_8 assump_35
      apply False.elim assump_27


variable (p6 p2 p1 : Prop)
theorem file16_23390 : ((((((p2 → False) ∨ (p6 → p1)) ∧ ((False → False) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_35 : ((((p2 → False) ∨ (p6 → p1)) ∧ ((False → False) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        have assump_36 : (False → False) := by
          intro assump_15
          apply False.elim assump_15
        let assump_14 := assump_7 assump_36
        apply False.elim assump_14
      case inr assump_9 =>
        have assump_37 : (False → False) := by
          intro assump_26
          apply False.elim assump_26
        let assump_25 := assump_7 assump_37
        apply False.elim assump_25
  let assump_4 := assump_1 assump_35
  apply False.elim assump_4


variable (p4 p7 p5 p0 : Prop)
theorem file16_24238 : ((((((p5 → False) → False) → ((p4 → True) ∨ (p7 ∧ p4))) ∨ (((p5 ∧ p5) → False) → ((p5 → False) ∧ (p0 ∨ p5)))) → False) → False) := by
  intro assump_13
  have assump_24 : ((((p5 → False) → False) → ((p4 → True) ∨ (p7 ∧ p4))) ∨ (((p5 ∧ p5) → False) → ((p5 → False) ∧ (p0 ∨ p5)))) := by
    apply Or.inl
    intro assump_17
    apply Or.inl
    intro assump_20
    apply True.intro
  let assump_16 := assump_13 assump_24
  apply False.elim assump_16


variable (p5 p7 p6 p3 p1 p4 : Prop)
theorem file16_24746 : (((((p3 ∧ p4) → (p5 ∧ True)) → ((p6 ∧ True) ∨ (p1 → p4))) ∧ (((p1 → False) → (p4 ∨ True)) → False)) → ((((p6 ∧ False) → (p3 → p7)) ∨ ((p7 ∧ True) → (p6 ∧ p1))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      have assump_35 : ((p1 → False) → (p4 ∨ True)) := by
        intro assump_14
        apply Or.inr
        apply True.intro
      let assump_13 := assump_8 assump_35
      apply False.elim assump_13
  case inr assump_4 =>
    cases assump_1
    case intro assump_22 assump_23 =>
      have assump_36 : ((p1 → False) → (p4 ∨ True)) := by
        intro assump_29
        apply Or.inr
        apply True.intro
      let assump_28 := assump_23 assump_36
      apply False.elim assump_28


variable (p3 p2 p7 p5 p1 p0 p6 : Prop)
theorem file16_25601 : ((((((p6 ∨ p2) ∨ (p0 ∧ p7)) ∧ ((p0 → p3) → False)) ∨ (((p5 ∧ False) ∧ (True ∧ p5)) → ((p1 → p6) → False))) → False) → False) := by
  intro assump_17
  have assump_36 : ((((p6 ∨ p2) ∨ (p0 ∧ p7)) ∧ ((p0 → p3) → False)) ∨ (((p5 ∧ False) ∧ (True ∧ p5)) → ((p1 → p6) → False))) := by
    apply Or.inr
    intro assump_21
    intro assump_22
    cases assump_21
    case intro assump_25 assump_26 =>
      cases assump_25
      case intro assump_27 assump_28 =>
        apply False.elim assump_28
  let assump_20 := assump_17 assump_36
  apply False.elim assump_20


variable (p0 p2 p7 p6 p3 p5 : Prop)
theorem file16_26220 : ((((((p6 → False) → False) → ((p6 ∨ p2) ∨ (p0 → False))) ∧ (((p0 ∧ p6) ∧ (p3 → False)) → ((True → False) → False))) ∧ ((((p5 ∨ True) ∨ (p2 → True)) ∨ ((p7 ∧ p2) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_16 : (((p5 ∨ True) ∨ (p2 → True)) ∨ ((p7 ∧ p2) → False)) := by
        apply Or.inl
        apply Or.inl
        apply Or.inr
        apply True.intro
      let assump_12 := assump_3 assump_16
      apply False.elim assump_12


variable (p2 p4 p1 p3 p5 p7 p6 : Prop)
theorem file16_26846 : ((((((p7 ∨ p1) ∧ (p6 ∨ p4)) → ((p6 ∧ p5) → False)) → (((p2 → False) ∨ (p4 → False)) ∨ ((p5 → False) ∨ (p7 → p1)))) ∧ ((((p6 ∨ p2) ∧ (p3 ∧ p5)) → ((p6 ∨ p3) ∨ (p4 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_33 : (((p6 ∨ p2) ∧ (p3 ∧ p5)) → ((p6 ∨ p3) ∨ (p4 → False))) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          cases assump_11
          case intro assump_16 assump_17 =>
            apply Or.inl
            apply Or.inl
            exact assump_12
        case inr assump_13 =>
          cases assump_11
          case intro assump_24 assump_25 =>
            apply Or.inl
            apply Or.inr
            exact assump_24
    let assump_8 := assump_3 assump_33
    apply False.elim assump_8


variable (p5 p3 p4 p7 p2 p1 p6 : Prop)
theorem file16_27788 : (((((True → False) → (p4 ∨ False)) → False) → (((p4 → p3) → False) ∧ ((p7 → p6) ∨ (p6 ∨ p6)))) ∨ ((((True ∧ p4) ∧ (p6 → p6)) ∧ ((p7 ∧ p4) ∧ (p2 → False))) ∧ (((p6 → p6) ∧ (p5 → p1)) → False))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  have assump_35 : ((True → False) → (p4 ∨ False)) := by
    intro assump_8
    have assump_36 : True := by
      apply True.intro
    let assump_11 := assump_8 assump_36
    apply False.elim assump_11
  let assump_7 := assump_1 assump_35
  apply False.elim assump_7
  apply Or.inl
  intro assump_20
  have assump_37 : ((True → False) → (p4 ∨ False)) := by
    intro assump_25
    have assump_38 : True := by
      apply True.intro
    let assump_28 := assump_25 assump_38
    apply False.elim assump_28
  let assump_24 := assump_1 assump_37
  apply False.elim assump_24


variable (p5 p7 p2 p6 p4 : Prop)
theorem file16_28682 : (((((True ∨ p2) → False) ∧ ((False → True) ∨ (p7 → p5))) → (((p4 ∨ True) → (p6 → True)) → ((p2 → False) → (p7 → False)))) ∨ ((((p2 → False) ∧ (p5 → False)) → False) → False)) := by
  apply Or.inl
  intro assump_14
  intro assump_15
  intro assump_16
  intro assump_17
  cases assump_14
  case intro assump_24 assump_25 =>
    cases assump_25
    case inl assump_28 =>
      have assump_45 : (True ∨ p2) := by
        apply Or.inl
        apply True.intro
      let assump_33 := assump_24 assump_45
      apply False.elim assump_33
    case inr assump_29 =>
      have assump_46 : (True ∨ p2) := by
        apply Or.inl
        apply True.intro
      let assump_41 := assump_24 assump_46
      apply False.elim assump_41


variable (p5 p1 p4 p0 p6 p2 p7 : Prop)
theorem file16_29465 : ((((((p6 → False) → False) ∧ ((p5 ∨ p6) → (p7 → p1))) → False) ∧ ((((p5 ∨ True) ∨ (p6 ∧ True)) → False) ∧ (((p0 ∧ p7) ∨ (p7 → p4)) ∨ ((p6 ∨ p2) → (p5 → p1))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        cases assump_10
        case inl assump_12 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            have assump_40 : ((p5 ∨ True) ∨ (p6 ∧ True)) := by
              apply Or.inl
              apply Or.inr
              apply True.intro
            let assump_22 := assump_6 assump_40
            apply False.elim assump_22
        case inr assump_13 =>
          have assump_41 : ((p5 ∨ True) ∨ (p6 ∧ True)) := by
            apply Or.inl
            apply Or.inr
            apply True.intro
          let assump_29 := assump_6 assump_41
          apply False.elim assump_29
      case inr assump_11 =>
        have assump_42 : ((p5 ∨ True) ∨ (p6 ∧ True)) := by
          apply Or.inl
          apply Or.inr
          apply True.intro
        let assump_36 := assump_6 assump_42
        apply False.elim assump_36


variable (p4 p3 p5 p0 p2 p7 p6 p1 : Prop)
theorem file16_30729 : (((((p6 ∧ False) → False) → ((True ∨ True) ∨ (p2 ∧ p1))) → False) → ((((False → p6) ∧ (p4 → False)) ∧ ((p4 → p3) ∨ (p0 ∨ False))) ∧ (((p6 → p6) ∧ (p5 ∧ p7)) → ((p7 ∨ False) → (True → True))))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  apply And.intro
  intro assump_2
  apply False.elim assump_2
  intro assump_5
  have assump_33 : (((p6 ∧ False) → False) → ((True ∨ True) ∨ (p2 ∧ p1))) := by
    intro assump_11
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_10 := assump_1 assump_33
  apply False.elim assump_10
  apply Or.inl
  intro assump_19
  have assump_34 : (((p6 ∧ False) → False) → ((True ∨ True) ∨ (p2 ∧ p1))) := by
    intro assump_24
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_23 := assump_1 assump_34
  apply False.elim assump_23
  intro assump_30
  intro assump_31
  intro assump_32
  apply True.intro


variable (p7 p6 p0 p1 p3 p2 : Prop)
theorem file16_31671 : (((((p6 ∧ p1) → False) ∧ ((p2 ∧ p7) ∨ (p7 ∨ p3))) → False) → ((((p1 → False) ∨ (p7 → False)) → ((p0 ∧ p0) → (p0 ∨ True))) ∨ (((p2 ∧ p0) ∨ (p1 → False)) ∧ ((p1 → False) → False)))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_4
    case inl assump_12 =>
      apply Or.inl
      exact assump_7
    case inr assump_13 =>
      apply Or.inl
      exact assump_7


variable (p3 p5 p4 p6 p7 p0 : Prop)
theorem file16_32185 : (((((p0 → p0) ∨ (p0 ∧ False)) ∨ ((True ∧ True) ∧ (False ∨ True))) ∨ (((False → p4) → False) → False)) ∨ ((((p4 → False) → False) ∧ ((p4 ∨ p7) ∧ (p0 ∧ p6))) ∧ (((p4 ∧ p6) → (p7 ∧ p6)) → ((True ∧ True) ∧ (p3 → p5))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  exact assump_1


variable (p2 p0 p4 p3 p7 p1 p6 p5 : Prop)
theorem file16_32567 : (((((True → False) ∧ (True ∨ True)) ∧ ((p4 ∧ p1) ∨ (p2 ∧ p5))) ∧ (((p6 ∧ p3) → False) ∧ ((p7 ∧ p3) → (p7 ∧ p6)))) → ((((p1 ∨ p0) ∨ (p4 ∧ p2)) → False) → (((True → p1) → False) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_1
  case intro assump_8 assump_9 =>
    cases assump_8
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_13
        case inl assump_16 =>
          cases assump_11
          case inl assump_20 =>
            cases assump_20
            case intro assump_22 assump_23 =>
              cases assump_9
              case intro assump_28 assump_29 =>
                have assump_106 : True := by
                  apply True.intro
                let assump_38 := assump_12 assump_106
                apply False.elim assump_38
          case inr assump_21 =>
            cases assump_21
            case intro assump_42 assump_43 =>
              cases assump_9
              case intro assump_48 assump_49 =>
                have assump_107 : True := by
                  apply True.intro
                let assump_58 := assump_12 assump_107
                apply False.elim assump_58
        case inr assump_17 =>
          cases assump_11
          case inl assump_64 =>
            cases assump_64
            case intro assump_66 assump_67 =>
              cases assump_9
              case intro assump_72 assump_73 =>
                have assump_108 : True := by
                  apply True.intro
                let assump_82 := assump_12 assump_108
                apply False.elim assump_82
          case inr assump_65 =>
            cases assump_65
            case intro assump_86 assump_87 =>
              cases assump_9
              case intro assump_92 assump_93 =>
                have assump_109 : True := by
                  apply True.intro
                let assump_102 := assump_12 assump_109
                apply False.elim assump_102


variable (p7 p1 p3 p2 p4 p0 p6 : Prop)
theorem file16_34622 : ((((((p7 → False) ∨ (p6 → False)) ∨ ((p2 ∧ p4) ∧ (False → p3))) → (((p1 ∨ p0) ∧ (p1 → p4)) → ((False → p2) ∨ (p0 → False)))) → False) → False) := by
  intro assump_1
  have assump_76 : ((((p7 → False) ∨ (p6 → False)) ∨ ((p2 ∧ p4) ∧ (False → p3))) → (((p1 ∨ p0) ∧ (p1 → p4)) → ((False → p2) ∨ (p0 → False)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_5
        case inl assump_15 =>
          cases assump_15
          case inl assump_17 =>
            apply Or.inl
            intro assump_21
            apply False.elim assump_21
          case inr assump_18 =>
            apply Or.inl
            intro assump_26
            apply False.elim assump_26
        case inr assump_16 =>
          cases assump_16
          case intro assump_29 assump_30 =>
            cases assump_29
            case intro assump_31 assump_32 =>
              apply Or.inl
              intro assump_39
              apply False.elim assump_39
      case inr assump_10 =>
        cases assump_5
        case inl assump_46 =>
          cases assump_46
          case inl assump_48 =>
            apply Or.inl
            intro assump_52
            apply False.elim assump_52
          case inr assump_49 =>
            apply Or.inl
            intro assump_57
            apply False.elim assump_57
        case inr assump_47 =>
          cases assump_47
          case intro assump_60 assump_61 =>
            cases assump_60
            case intro assump_62 assump_63 =>
              apply Or.inl
              intro assump_70
              apply False.elim assump_70
  let assump_4 := assump_1 assump_76
  apply False.elim assump_4


variable (p7 p2 p5 p1 p4 : Prop)
theorem file16_36425 : (((((p1 → p1) → False) → ((False ∨ p2) ∧ (p1 ∨ p2))) ∧ (((p1 → p7) → (p4 → p2)) → False)) → ((((p5 → False) → (True ∨ p1)) ∨ ((p7 → False) ∧ (True → False))) ∨ (((p2 → False) → (p7 → True)) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    apply Or.inl
    intro assump_8
    apply Or.inl
    apply True.intro


variable (p6 p4 p3 p5 p1 p2 p7 : Prop)
theorem file16_36854 : (((((True → False) ∨ (True ∧ p7)) → ((p1 → False) → False)) → (((True → p6) → (p4 → False)) ∨ ((False → False) → False))) → ((((p1 ∨ True) ∧ (p2 ∨ True)) ∨ ((False ∧ p3) ∨ (p2 → False))) ∨ (((p5 → p4) → False) ∧ ((p3 ∨ p6) → False)))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply And.intro
  apply Or.inr
  apply True.intro
  apply Or.inr
  apply True.intro


variable (p2 p3 p5 p1 p6 : Prop)
theorem file16_37285 : ((((((p1 → False) ∧ (True → False)) → False) → False) ∨ ((((True ∨ p2) → False) → ((p3 → p6) → (p5 ∨ p2))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_37 : (((p1 → False) ∧ (True → False)) → False) := by
      intro assump_7
      cases assump_7
      case intro assump_8 assump_9 =>
        have assump_38 : True := by
          apply True.intro
        let assump_14 := assump_9 assump_38
        apply False.elim assump_14
    let assump_6 := assump_2 assump_37
    apply False.elim assump_6
  case inr assump_3 =>
    have assump_39 : (((True ∨ p2) → False) → ((p3 → p6) → (p5 ∨ p2))) := by
      intro assump_24
      intro assump_25
      have assump_40 : (True ∨ p2) := by
        apply Or.inl
        apply True.intro
      let assump_30 := assump_24 assump_40
      apply False.elim assump_30
    let assump_23 := assump_3 assump_39
    apply False.elim assump_23


variable (p1 p4 p7 p5 p2 p0 : Prop)
theorem file16_38272 : ((((((p4 → False) ∧ (p7 ∨ p1)) ∨ ((p2 → p5) ∨ (p2 → False))) → (((p5 ∧ p4) → (p0 → False)) → ((True → False) → (p2 → p1)))) → False) → False) := by
  intro assump_1
  have assump_54 : ((((p4 → False) ∧ (p7 ∨ p1)) ∨ ((p2 → p5) ∨ (p2 → False))) → (((p5 ∧ p4) → (p0 → False)) → ((True → False) → (p2 → p1)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    cases assump_5
    case inl assump_15 =>
      cases assump_15
      case intro assump_17 assump_18 =>
        cases assump_18
        case inl assump_21 =>
          have assump_55 : True := by
            apply True.intro
          let assump_28 := assump_7 assump_55
          apply False.elim assump_28
        case inr assump_22 =>
          exact assump_22
    case inr assump_16 =>
      cases assump_16
      case inl assump_34 =>
        have assump_56 : True := by
          apply True.intro
        let assump_41 := assump_7 assump_56
        apply False.elim assump_41
      case inr assump_35 =>
        have assump_57 : p2 := by
          exact assump_8
        let assump_47 := assump_35 assump_57
        apply False.elim assump_47
  let assump_4 := assump_1 assump_54
  apply False.elim assump_4


variable (p1 p4 p7 p3 p0 : Prop)
theorem file16_39534 : ((((((p4 → False) → (p3 → False)) ∨ ((True ∨ p4) → (p7 → False))) ∧ (((p3 ∧ p3) → False) ∧ ((p1 → False) → False))) ∧ ((((False ∧ p4) → (p1 → False)) ∨ ((False ∧ True) → (p0 ∧ p0))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_5
        case intro assump_10 assump_11 =>
          have assump_52 : (((False ∧ p4) → (p1 → False)) ∨ ((False ∧ True) → (p0 ∧ p0))) := by
            apply Or.inl
            intro assump_19
            intro assump_20
            cases assump_19
            case intro assump_23 assump_24 =>
              apply False.elim assump_23
          let assump_18 := assump_3 assump_52
          apply False.elim assump_18
      case inr assump_7 =>
        cases assump_5
        case intro assump_32 assump_33 =>
          have assump_53 : (((False ∧ p4) → (p1 → False)) ∨ ((False ∧ True) → (p0 ∧ p0))) := by
            apply Or.inl
            intro assump_41
            intro assump_42
            cases assump_41
            case intro assump_45 assump_46 =>
              apply False.elim assump_45
          let assump_40 := assump_3 assump_53
          apply False.elim assump_40


variable (p6 p0 p1 p4 p2 p7 p5 p3 : Prop)
theorem file16_40885 : (((((False → False) ∨ (p7 → p4)) → False) ∧ (((p1 → p3) → (p3 ∨ True)) ∨ ((p3 → False) ∧ (False ∨ p2)))) → ((((p7 ∧ p1) ∧ (p6 ∨ False)) ∧ ((p2 ∧ True) → (p3 ∨ True))) → (((False ∧ p5) ∧ (p5 ∧ p5)) ∨ ((p5 ∧ p0) ∨ (True → p1))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        cases assump_6
        case inl assump_13 =>
          cases assump_1
          case intro assump_19 assump_20 =>
            cases assump_20
            case inl assump_23 =>
              apply Or.inr
              apply Or.inr
              intro assump_27
              exact assump_8
            case inr assump_24 =>
              cases assump_24
              case intro assump_30 assump_31 =>
                cases assump_31
                case inl assump_34 =>
                  apply False.elim assump_34
                case inr assump_35 =>
                  apply Or.inr
                  apply Or.inr
                  intro assump_40
                  exact assump_8
        case inr assump_14 =>
          apply False.elim assump_14


variable (p2 p0 p3 p6 p1 : Prop)
theorem file16_42133 : (((((p1 ∧ p6) → False) → ((p2 → True) ∨ (p0 → p2))) → False) → ((((p2 ∨ p2) → False) ∧ ((p3 → False) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    have assump_19 : (((p1 ∧ p6) → False) → ((p2 → True) ∨ (p0 → p2))) := by
      intro assump_12
      apply Or.inl
      intro assump_15
      apply True.intro
    let assump_11 := assump_1 assump_19
    apply False.elim assump_11


variable (p1 p5 p6 p7 p4 : Prop)
theorem file16_42636 : (((((p4 ∧ True) → False) → ((True ∨ p6) ∨ (True → p6))) → False) → ((((p7 ∧ p7) → (True → False)) ∨ ((p5 ∨ p1) → (p6 → p4))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    have assump_27 : (((p4 ∧ True) → False) → ((True ∨ p6) ∨ (True → p6))) := by
      intro assump_10
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_9 := assump_1 assump_27
    apply False.elim assump_9
  case inr assump_4 =>
    have assump_28 : (((p4 ∧ True) → False) → ((True ∨ p6) ∨ (True → p6))) := by
      intro assump_21
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_20 := assump_1 assump_28
    apply False.elim assump_20


variable (p5 p1 p2 p3 p4 p7 p0 : Prop)
theorem file16_43405 : (((((True → False) ∧ (p3 ∧ p2)) → ((p5 → False) ∨ (True ∧ p7))) ∨ (((False → p5) ∨ (p4 → p0)) → False)) ∨ ((((p7 ∨ p2) → False) → ((p1 ∧ p3) → False)) → (((p5 → p2) ∨ (p0 ∨ p3)) ∧ ((p2 ∧ False) → (p7 → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      apply Or.inl
      intro assump_12
      have assump_22 : True := by
        apply True.intro
      let assump_18 := assump_2 assump_22
      apply False.elim assump_18


variable (p3 p7 p6 p0 p5 p1 : Prop)
theorem file16_44012 : (((((p0 → p3) ∨ (False → False)) → ((True ∨ p5) → (p0 ∧ False))) → (((p7 ∨ p3) → (p6 ∨ p7)) ∧ ((True ∧ False) ∨ (p1 → p1)))) ∨ ((((p5 ∨ p5) → (p6 ∨ p1)) → ((p5 → False) ∨ (p3 ∨ p6))) → False)) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    apply Or.inr
    exact assump_3
  case inr assump_4 =>
    have assump_28 : ((p0 → p3) ∨ (False → False)) := by
      apply Or.inl
      intro assump_14
      exact assump_4
    let assump_13 := assump_1 assump_28
    have assump_29 : (True ∨ p5) := by
      apply Or.inl
      apply True.intro
    let assump_17 := assump_13 assump_29
    let assump_18 := And.right assump_17
    apply False.elim assump_18
  apply Or.inr
  intro assump_25
  exact assump_25


variable (p0 p3 p2 p7 p1 p5 p6 : Prop)
theorem file16_44844 : (((((p1 ∧ p0) → (p7 → False)) → False) ∧ (((p2 → p1) → (p5 → p1)) ∨ ((p1 ∧ p2) ∨ (p5 → False)))) → ((((p2 → p5) ∧ (False → False)) ∧ ((p3 ∧ p6) ∨ (p1 ∨ p7))) → (((p2 → False) ∨ (p6 → p0)) → ((p1 ∧ p6) → (p1 ∧ p6))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  apply And.intro
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_3
    case inl assump_11 =>
      cases assump_2
      case intro assump_15 assump_16 =>
        cases assump_15
        case intro assump_17 assump_18 =>
          cases assump_16
          case inl assump_23 =>
            cases assump_23
            case intro assump_25 assump_26 =>
              cases assump_1
              case intro assump_31 assump_32 =>
                cases assump_32
                case inl assump_35 =>
                  exact assump_5
                case inr assump_36 =>
                  cases assump_36
                  case inl assump_39 =>
                    cases assump_39
                    case intro assump_41 assump_42 =>
                      exact assump_41
                  case inr assump_40 =>
                    exact assump_5
          case inr assump_24 =>
            cases assump_24
            case inl assump_49 =>
              cases assump_1
              case intro assump_53 assump_54 =>
                cases assump_54
                case inl assump_57 =>
                  exact assump_49
                case inr assump_58 =>
                  cases assump_58
                  case inl assump_61 =>
                    cases assump_61
                    case intro assump_63 assump_64 =>
                      exact assump_63
                  case inr assump_62 =>
                    exact assump_49
            case inr assump_50 =>
              cases assump_1
              case intro assump_73 assump_74 =>
                cases assump_74
                case inl assump_77 =>
                  exact assump_5
                case inr assump_78 =>
                  cases assump_78
                  case inl assump_81 =>
                    cases assump_81
                    case intro assump_83 assump_84 =>
                      exact assump_83
                  case inr assump_82 =>
                    exact assump_5
    case inr assump_12 =>
      cases assump_2
      case intro assump_93 assump_94 =>
        cases assump_93
        case intro assump_95 assump_96 =>
          cases assump_94
          case inl assump_101 =>
            cases assump_101
            case intro assump_103 assump_104 =>
              cases assump_1
              case intro assump_109 assump_110 =>
                cases assump_110
                case inl assump_113 =>
                  exact assump_5
                case inr assump_114 =>
                  cases assump_114
                  case inl assump_117 =>
                    cases assump_117
                    case intro assump_119 assump_120 =>
                      exact assump_119
                  case inr assump_118 =>
                    exact assump_5
          case inr assump_102 =>
            cases assump_102
            case inl assump_127 =>
              cases assump_1
              case intro assump_131 assump_132 =>
                cases assump_132
                case inl assump_135 =>
                  exact assump_127
                case inr assump_136 =>
                  cases assump_136
                  case inl assump_139 =>
                    cases assump_139
                    case intro assump_141 assump_142 =>
                      exact assump_141
                  case inr assump_140 =>
                    exact assump_127
            case inr assump_128 =>
              cases assump_1
              case intro assump_151 assump_152 =>
                cases assump_152
                case inl assump_155 =>
                  exact assump_5
                case inr assump_156 =>
                  cases assump_156
                  case inl assump_159 =>
                    cases assump_159
                    case intro assump_161 assump_162 =>
                      exact assump_161
                  case inr assump_160 =>
                    exact assump_5
  cases assump_4
  case intro assump_169 assump_170 =>
    cases assump_3
    case inl assump_175 =>
      cases assump_2
      case intro assump_179 assump_180 =>
        cases assump_179
        case intro assump_181 assump_182 =>
          cases assump_180
          case inl assump_187 =>
            cases assump_187
            case intro assump_189 assump_190 =>
              cases assump_1
              case intro assump_195 assump_196 =>
                cases assump_196
                case inl assump_199 =>
                  exact assump_190
                case inr assump_200 =>
                  cases assump_200
                  case inl assump_203 =>
                    cases assump_203
                    case intro assump_205 assump_206 =>
                      exact assump_190
                  case inr assump_204 =>
                    exact assump_190
          case inr assump_188 =>
            cases assump_188
            case inl assump_213 =>
              cases assump_1
              case intro assump_217 assump_218 =>
                cases assump_218
                case inl assump_221 =>
                  exact assump_170
                case inr assump_222 =>
                  cases assump_222
                  case inl assump_225 =>
                    cases assump_225
                    case intro assump_227 assump_228 =>
                      exact assump_170
                  case inr assump_226 =>
                    exact assump_170
            case inr assump_214 =>
              cases assump_1
              case intro assump_237 assump_238 =>
                cases assump_238
                case inl assump_241 =>
                  exact assump_170
                case inr assump_242 =>
                  cases assump_242
                  case inl assump_245 =>
                    cases assump_245
                    case intro assump_247 assump_248 =>
                      exact assump_170
                  case inr assump_246 =>
                    exact assump_170
    case inr assump_176 =>
      cases assump_2
      case intro assump_257 assump_258 =>
        cases assump_257
        case intro assump_259 assump_260 =>
          cases assump_258
          case inl assump_265 =>
            cases assump_265
            case intro assump_267 assump_268 =>
              cases assump_1
              case intro assump_273 assump_274 =>
                cases assump_274
                case inl assump_277 =>
                  exact assump_268
                case inr assump_278 =>
                  cases assump_278
                  case inl assump_281 =>
                    cases assump_281
                    case intro assump_283 assump_284 =>
                      exact assump_268
                  case inr assump_282 =>
                    exact assump_268
          case inr assump_266 =>
            cases assump_266
            case inl assump_291 =>
              cases assump_1
              case intro assump_295 assump_296 =>
                cases assump_296
                case inl assump_299 =>
                  exact assump_170
                case inr assump_300 =>
                  cases assump_300
                  case inl assump_303 =>
                    cases assump_303
                    case intro assump_305 assump_306 =>
                      exact assump_170
                  case inr assump_304 =>
                    exact assump_170
            case inr assump_292 =>
              cases assump_1
              case intro assump_315 assump_316 =>
                cases assump_316
                case inl assump_319 =>
                  exact assump_170
                case inr assump_320 =>
                  cases assump_320
                  case inl assump_323 =>
                    cases assump_323
                    case intro assump_325 assump_326 =>
                      exact assump_170
                  case inr assump_324 =>
                    exact assump_170


variable (p1 p2 p0 p3 : Prop)
theorem file16_53119 : (((((p1 ∧ p1) ∧ (False ∧ p3)) ∧ ((p3 ∨ p1) ∧ (True ∨ False))) → False) → ((((True → False) → (p2 ∨ p2)) ∧ ((True ∧ False) ∧ (p0 ∧ p2))) → False)) := by
  intro assump_18
  intro assump_19
  cases assump_19
  case intro assump_20 assump_21 =>
    cases assump_21
    case intro assump_24 assump_25 =>
      cases assump_24
      case intro assump_26 assump_27 =>
        apply False.elim assump_27


variable (p2 p7 p0 p5 p6 p1 p3 p4 : Prop)
theorem file16_53582 : (((((False ∧ p3) ∧ (p7 ∨ p0)) → ((p1 ∧ p1) ∧ (p3 → False))) ∨ (((p5 ∨ p0) → (p5 → p0)) ∧ ((p1 ∧ p2) ∧ (p5 → p6)))) ∨ ((((p6 → p2) ∧ (True ∨ p6)) ∧ ((p2 ∨ p4) ∨ (p4 → False))) ∨ (((p0 → False) ∧ (p1 ∨ p2)) ∧ ((p3 ∨ False) ∧ (p1 → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply And.intro
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply False.elim assump_4
  cases assump_1
  case intro assump_8 assump_9 =>
    cases assump_8
    case intro assump_10 assump_11 =>
      apply False.elim assump_10
  intro assump_14
  cases assump_1
  case intro assump_17 assump_18 =>
    cases assump_17
    case intro assump_19 assump_20 =>
      apply False.elim assump_19


variable (p7 p5 p1 p4 p0 p3 p6 : Prop)
theorem file16_54415 : (((((p4 → False) ∨ (p5 → p3)) ∨ ((p3 ∨ p3) ∨ (p3 ∧ True))) → False) → ((((False → True) → False) → ((False ∧ p6) → (p7 ∧ p5))) ∨ (((p6 → False) ∧ (p1 ∨ p4)) → ((p0 ∧ p5) → False)))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  apply And.intro
  cases assump_5
  case intro assump_6 assump_7 =>
    apply False.elim assump_6
  cases assump_5
  case intro assump_10 assump_11 =>
    apply False.elim assump_10


variable (p2 p3 p7 p0 p5 p4 p6 : Prop)
theorem file16_54915 : (((((p6 ∧ p2) → (True ∧ False)) ∨ ((p4 → False) ∨ (True ∨ p4))) → (((False → p2) → False) → False)) ∨ ((((p0 → p5) ∨ (p7 ∧ p7)) → ((p5 → p5) → False)) ∧ (((p5 → True) ∨ (False → False)) ∨ ((p3 ∨ p4) → False)))) := by
  apply Or.inl
  intro assump_5
  intro assump_6
  cases assump_5
  case inl assump_9 =>
    have assump_54 : (False → p2) := by
      intro assump_15
      apply False.elim assump_15
    let assump_14 := assump_6 assump_54
    apply False.elim assump_14
  case inr assump_10 =>
    cases assump_10
    case inl assump_21 =>
      have assump_55 : (False → p2) := by
        intro assump_27
        apply False.elim assump_27
      let assump_26 := assump_6 assump_55
      apply False.elim assump_26
    case inr assump_22 =>
      cases assump_22
      case inl assump_33 =>
        have assump_56 : (False → p2) := by
          intro assump_38
          apply False.elim assump_38
        let assump_37 := assump_6 assump_56
        apply False.elim assump_37
      case inr assump_34 =>
        have assump_57 : (False → p2) := by
          intro assump_48
          apply False.elim assump_48
        let assump_47 := assump_6 assump_57
        apply False.elim assump_47


variable (p2 p0 p1 p3 p5 p4 p7 p6 : Prop)
theorem file16_56175 : (((((p1 → p3) → False) → ((p6 → p0) → (p2 ∨ p7))) → False) → ((((False ∨ p4) ∨ (p2 → False)) ∧ ((p1 ∧ p4) ∧ (p7 → False))) → (((p2 → False) ∨ (p1 → p3)) ∧ ((p4 ∧ p5) ∨ (p6 ∨ p1))))) := by
  intro assump_28
  intro assump_29
  apply And.intro
  cases assump_29
  case intro assump_30 assump_31 =>
    cases assump_30
    case inl assump_32 =>
      cases assump_32
      case inl assump_34 =>
        apply False.elim assump_34
      case inr assump_35 =>
        cases assump_31
        case intro assump_40 assump_41 =>
          cases assump_40
          case intro assump_42 assump_43 =>
            apply Or.inl
            intro assump_52
            have assump_130 : (((p1 → p3) → False) → ((p6 → p0) → (p2 ∨ p7))) := by
              intro assump_57
              intro assump_58
              apply Or.inl
              exact assump_52
            let assump_56 := assump_28 assump_130
            apply False.elim assump_56
    case inr assump_33 =>
      cases assump_31
      case intro assump_68 assump_69 =>
        cases assump_68
        case intro assump_70 assump_71 =>
          apply Or.inl
          intro assump_80
          have assump_131 : (((p1 → p3) → False) → ((p6 → p0) → (p2 ∨ p7))) := by
            intro assump_85
            intro assump_86
            apply Or.inl
            exact assump_80
          let assump_84 := assump_28 assump_131
          apply False.elim assump_84
  cases assump_29
  case intro assump_94 assump_95 =>
    cases assump_94
    case inl assump_96 =>
      cases assump_96
      case inl assump_98 =>
        apply False.elim assump_98
      case inr assump_99 =>
        cases assump_95
        case intro assump_104 assump_105 =>
          cases assump_104
          case intro assump_106 assump_107 =>
            apply Or.inr
            apply Or.inr
            exact assump_106
    case inr assump_97 =>
      cases assump_95
      case intro assump_118 assump_119 =>
        cases assump_118
        case intro assump_120 assump_121 =>
          apply Or.inr
          apply Or.inr
          exact assump_120


variable (p7 p5 p0 p4 p6 p3 p2 : Prop)
theorem file16_58316 : ((((((p7 ∧ p4) ∧ (p5 ∧ True)) ∧ ((p2 → p3) ∨ (p5 → False))) ∧ (((p3 ∧ p4) ∧ (p7 ∧ p7)) ∧ ((p6 → False) ∨ (True ∨ p3)))) ∧ ((((p0 ∧ False) ∨ (p4 → p5)) ∨ ((p2 → False) ∧ (False → False))) → False)) → False) := by
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
            cases assump_9
            case intro assump_16 assump_17 =>
              cases assump_7
              case inl assump_22 =>
                cases assump_5
                case intro assump_26 assump_27 =>
                  cases assump_26
                  case intro assump_28 assump_29 =>
                    cases assump_28
                    case intro assump_30 assump_31 =>
                      cases assump_29
                      case intro assump_36 assump_37 =>
                        cases assump_27
                        case inl assump_42 =>
                          have assump_134 : (((p0 ∧ False) ∨ (p4 → p5)) ∨ ((p2 → False) ∧ (False → False))) := by
                            apply Or.inl
                            apply Or.inr
                            intro assump_49
                            exact assump_16
                          let assump_48 := assump_3 assump_134
                          apply False.elim assump_48
                        case inr assump_43 =>
                          cases assump_43
                          case inl assump_55 =>
                            have assump_135 : (((p0 ∧ False) ∨ (p4 → p5)) ∨ ((p2 → False) ∧ (False → False))) := by
                              apply Or.inl
                              apply Or.inr
                              intro assump_62
                              exact assump_16
                            let assump_61 := assump_3 assump_135
                            apply False.elim assump_61
                          case inr assump_56 =>
                            have assump_136 : (((p0 ∧ False) ∨ (p4 → p5)) ∨ ((p2 → False) ∧ (False → False))) := by
                              apply Or.inl
                              apply Or.inr
                              intro assump_73
                              exact assump_16
                            let assump_72 := assump_3 assump_136
                            apply False.elim assump_72
              case inr assump_23 =>
                cases assump_5
                case intro assump_81 assump_82 =>
                  cases assump_81
                  case intro assump_83 assump_84 =>
                    cases assump_83
                    case intro assump_85 assump_86 =>
                      cases assump_84
                      case intro assump_91 assump_92 =>
                        cases assump_82
                        case inl assump_97 =>
                          have assump_137 : (((p0 ∧ False) ∨ (p4 → p5)) ∨ ((p2 → False) ∧ (False → False))) := by
                            apply Or.inl
                            apply Or.inr
                            intro assump_104
                            exact assump_16
                          let assump_103 := assump_3 assump_137
                          apply False.elim assump_103
                        case inr assump_98 =>
                          cases assump_98
                          case inl assump_110 =>
                            have assump_138 : (((p0 ∧ False) ∨ (p4 → p5)) ∨ ((p2 → False) ∧ (False → False))) := by
                              apply Or.inl
                              apply Or.inr
                              intro assump_117
                              exact assump_16
                            let assump_116 := assump_3 assump_138
                            apply False.elim assump_116
                          case inr assump_111 =>
                            have assump_139 : (((p0 ∧ False) ∨ (p4 → p5)) ∨ ((p2 → False) ∧ (False → False))) := by
                              apply Or.inl
                              apply Or.inr
                              intro assump_128
                              exact assump_16
                            let assump_127 := assump_3 assump_139
                            apply False.elim assump_127


variable (p4 p1 p6 p0 p3 p5 p2 : Prop)
theorem file16_62788 : (((((True → False) ∧ (p4 → False)) → ((p0 → False) ∧ (p3 ∧ p5))) ∨ (((True ∧ p2) ∧ (p1 → False)) → False)) → ((((p2 → p2) → False) → ((p6 → False) → (True ∨ p2))) ∨ (((True ∧ p0) ∨ (p6 ∨ p4)) → False))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    intro assump_7
    apply Or.inl
    apply True.intro
  case inr assump_3 =>
    apply Or.inl
    intro assump_14
    intro assump_15
    apply Or.inl
    apply True.intro


variable (p0 p7 p4 p1 p2 : Prop)
theorem file16_63322 : (((((False → False) ∧ (p2 ∨ p2)) → False) ∧ (((p4 → False) ∨ (p0 → False)) → False)) → ((((True ∨ p7) ∨ (p2 → p7)) → False) → (((p1 ∧ p1) → False) → ((False ∧ p7) → False)))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply False.elim assump_5


variable (p3 p6 p2 p4 p7 p1 p0 p5 : Prop)
theorem file16_63718 : (((((p1 → p3) ∧ (p6 → False)) → False) → (((p7 → p3) → (p6 → False)) → ((p2 ∧ p3) → (False → False)))) ∨ ((((p2 → p2) ∧ (p2 ∧ p7)) ∧ ((p4 → p2) ∧ (True → p1))) ∧ (((p0 ∨ p1) ∨ (p4 ∨ p5)) → ((p4 → p0) → (p5 → p7))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  apply False.elim assump_4


variable (p2 p5 p0 p3 p1 p4 : Prop)
theorem file16_64111 : ((((((True ∨ p3) → False) → ((p2 → False) → False)) ∨ (((p2 ∨ p5) ∨ (p2 → False)) ∨ ((p1 ∧ p0) ∨ (p5 ∨ p3)))) ∧ ((((False ∧ p4) ∧ (p5 → p3)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_125 : (((False ∧ p4) ∧ (p5 → p3)) → False) := by
        intro assump_11
        cases assump_11
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            apply False.elim assump_14
      let assump_10 := assump_3 assump_125
      apply False.elim assump_10
    case inr assump_5 =>
      cases assump_5
      case inl assump_21 =>
        cases assump_21
        case inl assump_23 =>
          cases assump_23
          case inl assump_25 =>
            have assump_126 : (((False ∧ p4) ∧ (p5 → p3)) → False) := by
              intro assump_32
              cases assump_32
              case intro assump_33 assump_34 =>
                cases assump_33
                case intro assump_35 assump_36 =>
                  apply False.elim assump_35
            let assump_31 := assump_3 assump_126
            apply False.elim assump_31
          case inr assump_26 =>
            have assump_127 : (((False ∧ p4) ∧ (p5 → p3)) → False) := by
              intro assump_47
              cases assump_47
              case intro assump_48 assump_49 =>
                cases assump_48
                case intro assump_50 assump_51 =>
                  apply False.elim assump_50
            let assump_46 := assump_3 assump_127
            apply False.elim assump_46
        case inr assump_24 =>
          have assump_128 : (((False ∧ p4) ∧ (p5 → p3)) → False) := by
            intro assump_62
            cases assump_62
            case intro assump_63 assump_64 =>
              cases assump_63
              case intro assump_65 assump_66 =>
                apply False.elim assump_65
          let assump_61 := assump_3 assump_128
          apply False.elim assump_61
      case inr assump_22 =>
        cases assump_22
        case inl assump_72 =>
          cases assump_72
          case intro assump_74 assump_75 =>
            have assump_129 : (((False ∧ p4) ∧ (p5 → p3)) → False) := by
              intro assump_83
              cases assump_83
              case intro assump_84 assump_85 =>
                cases assump_84
                case intro assump_86 assump_87 =>
                  apply False.elim assump_86
            let assump_82 := assump_3 assump_129
            apply False.elim assump_82
        case inr assump_73 =>
          cases assump_73
          case inl assump_93 =>
            have assump_130 : (((False ∧ p4) ∧ (p5 → p3)) → False) := by
              intro assump_100
              cases assump_100
              case intro assump_101 assump_102 =>
                cases assump_101
                case intro assump_103 assump_104 =>
                  apply False.elim assump_103
            let assump_99 := assump_3 assump_130
            apply False.elim assump_99
          case inr assump_94 =>
            have assump_131 : (((False ∧ p4) ∧ (p5 → p3)) → False) := by
              intro assump_115
              cases assump_115
              case intro assump_116 assump_117 =>
                cases assump_116
                case intro assump_118 assump_119 =>
                  apply False.elim assump_118
            let assump_114 := assump_3 assump_131
            apply False.elim assump_114


variable (p0 p6 p2 p7 p4 p3 p1 : Prop)
theorem file16_67699 : (((((True → False) → (p6 → False)) ∨ ((True → False) ∧ (p7 → False))) → (((p7 → False) → (p4 ∨ p0)) → False)) → ((((p3 → p1) → (True ∨ True)) ∨ ((p4 ∨ p1) ∧ (p2 → True))) ∨ (((p2 → False) → (p4 ∧ p6)) ∨ ((True → False) → (True ∧ p1))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  apply Or.inl
  apply True.intro


variable (p2 p3 p7 p6 p0 p1 p5 p4 : Prop)
theorem file16_68106 : ((((((p1 ∧ p0) → False) → False) → (((p0 ∧ p6) ∨ (True → p7)) ∧ ((p6 ∧ p5) → False))) ∧ ((((False ∧ p3) ∨ (p4 → True)) → False) ∧ (((p0 → False) ∨ (p2 ∨ p7)) ∨ ((True ∨ p4) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        cases assump_10
        case inl assump_12 =>
          have assump_46 : ((False ∧ p3) ∨ (p4 → True)) := by
            apply Or.inr
            intro assump_18
            apply True.intro
          let assump_17 := assump_6 assump_46
          apply False.elim assump_17
        case inr assump_13 =>
          cases assump_13
          case inl assump_22 =>
            have assump_47 : ((False ∧ p3) ∨ (p4 → True)) := by
              apply Or.inr
              intro assump_28
              apply True.intro
            let assump_27 := assump_6 assump_47
            apply False.elim assump_27
          case inr assump_23 =>
            have assump_48 : ((False ∧ p3) ∨ (p4 → True)) := by
              apply Or.inr
              intro assump_36
              apply True.intro
            let assump_35 := assump_6 assump_48
            apply False.elim assump_35
      case inr assump_11 =>
        have assump_49 : (True ∨ p4) := by
          apply Or.inl
          apply True.intro
        let assump_42 := assump_11 assump_49
        apply False.elim assump_42


variable (p0 p1 p6 p2 p7 p5 p4 p3 : Prop)
theorem file16_69624 : ((((((p0 → p2) ∨ (p3 → p5)) ∨ ((p2 ∧ p1) → False)) → (((p3 ∧ p6) ∧ (True → False)) → ((p3 → False) ∨ (p3 ∨ p5)))) ∧ ((((p2 → p7) → (p7 → True)) ∨ ((p4 ∨ p7) → (p0 ∨ p6))) → False)) → False) := by
  intro assump_15
  cases assump_15
  case intro assump_16 assump_17 =>
    have assump_28 : (((p2 → p7) → (p7 → True)) ∨ ((p4 ∨ p7) → (p0 ∨ p6))) := by
      apply Or.inl
      intro assump_23
      intro assump_24
      apply True.intro
    let assump_22 := assump_17 assump_28
    apply False.elim assump_22


variable (p4 p7 p2 p5 p6 p3 : Prop)
theorem file16_70191 : ((((((p7 → True) → False) → False) ∨ (((p2 ∨ p6) ∨ (p4 → False)) ∨ ((p5 ∨ p5) → (p3 ∧ p2)))) → False) → False) := by
  intro assump_1
  have assump_16 : ((((p7 → True) → False) → False) ∨ (((p2 ∨ p6) ∨ (p4 → False)) ∨ ((p5 ∨ p5) → (p3 ∧ p2)))) := by
    apply Or.inl
    intro assump_5
    have assump_17 : (p7 → True) := by
      intro assump_9
      apply True.intro
    let assump_8 := assump_5 assump_17
    apply False.elim assump_8
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p2 p4 p5 p3 p6 p7 p0 p1 : Prop)
theorem file16_70760 : ((((((p3 → p5) → (True → p2)) → ((p7 ∧ p2) → (p0 → False))) ∨ (((p7 ∨ p4) ∨ (p0 ∧ p6)) ∨ ((p3 ∨ p0) → False))) ∧ ((((False ∧ p1) ∧ (p2 ∧ p2)) ∧ ((p5 ∧ p2) → False)) ∧ (((p2 → False) ∨ (p6 ∧ p5)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            cases assump_12
            case intro assump_14 assump_15 =>
              apply False.elim assump_14
    case inr assump_5 =>
      cases assump_5
      case inl assump_18 =>
        cases assump_18
        case inl assump_20 =>
          cases assump_20
          case inl assump_22 =>
            cases assump_3
            case intro assump_26 assump_27 =>
              cases assump_26
              case intro assump_28 assump_29 =>
                cases assump_28
                case intro assump_30 assump_31 =>
                  cases assump_30
                  case intro assump_32 assump_33 =>
                    apply False.elim assump_32
          case inr assump_23 =>
            cases assump_3
            case intro assump_38 assump_39 =>
              cases assump_38
              case intro assump_40 assump_41 =>
                cases assump_40
                case intro assump_42 assump_43 =>
                  cases assump_42
                  case intro assump_44 assump_45 =>
                    apply False.elim assump_44
        case inr assump_21 =>
          cases assump_21
          case intro assump_48 assump_49 =>
            cases assump_3
            case intro assump_54 assump_55 =>
              cases assump_54
              case intro assump_56 assump_57 =>
                cases assump_56
                case intro assump_58 assump_59 =>
                  cases assump_58
                  case intro assump_60 assump_61 =>
                    apply False.elim assump_60
      case inr assump_19 =>
        cases assump_3
        case intro assump_66 assump_67 =>
          cases assump_66
          case intro assump_68 assump_69 =>
            cases assump_68
            case intro assump_70 assump_71 =>
              cases assump_70
              case intro assump_72 assump_73 =>
                apply False.elim assump_72


variable (p5 p1 p3 p7 : Prop)
theorem file16_73230 : (((((p5 → p5) → (False ∨ True)) ∧ ((False → False) → (p1 → True))) → False) → ((((False → False) → False) → ((p7 ∨ p7) ∧ (p3 ∧ p7))) → (((p1 → False) → False) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  have assump_19 : (((p5 → p5) → (False ∨ True)) ∧ ((False → False) → (p1 → True))) := by
    apply And.intro
    intro assump_11
    apply Or.inr
    apply True.intro
    intro assump_14
    intro assump_15
    apply True.intro
  let assump_10 := assump_1 assump_19
  apply False.elim assump_10


variable (p7 p6 p2 p0 p1 : Prop)
theorem file16_73810 : ((((((p7 ∨ p6) ∧ (p0 ∧ p1)) ∨ ((True → False) → False)) → (((p2 → False) ∧ (False ∧ True)) → False)) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p7 ∨ p6) ∧ (p0 ∧ p1)) ∨ ((True → False) → False)) → (((p2 → False) ∧ (False ∧ True)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        apply False.elim assump_11
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p1 p7 p4 p0 p6 p3 p2 : Prop)
theorem file16_74393 : (((((p3 → False) → (p2 → True)) ∨ ((p1 → p0) → (False → p6))) ∨ (((p6 ∧ p3) ∧ (p3 ∧ p0)) → False)) ∨ ((((p7 ∨ p1) → (p6 → False)) → False) ∨ (((p4 → False) ∨ (p0 → p6)) → False))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  apply True.intro


variable (p2 p3 p5 p6 p7 p1 : Prop)
theorem file16_74737 : ((((((p5 ∧ p5) → (p3 → False)) → ((p2 ∨ p6) ∧ (p3 → p2))) ∧ (((p1 ∧ p7) → (True → False)) ∧ ((False → p5) → False))) ∧ ((((False → False) ∨ (True → p2)) ∨ ((p7 ∨ p6) → (p3 ∨ p2))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        have assump_23 : (((False → False) ∨ (True → p2)) ∨ ((p7 ∨ p6) → (p3 ∨ p2))) := by
          apply Or.inl
          apply Or.inl
          intro assump_17
          apply False.elim assump_17
        let assump_16 := assump_3 assump_23
        apply False.elim assump_16


variable (p7 p2 p5 p3 p0 p4 : Prop)
theorem file16_75463 : ((((((p5 ∧ p2) ∧ (p0 → False)) ∧ ((p0 ∧ p3) ∨ (False ∧ p5))) → (((p4 ∨ p7) → (p0 → False)) ∨ ((False → False) ∨ (p5 → False)))) → False) → False) := by
  intro assump_1
  have assump_59 : ((((p5 ∧ p2) ∧ (p0 → False)) ∧ ((p0 ∧ p3) ∨ (False ∧ p5))) → (((p4 ∨ p7) → (p0 → False)) ∨ ((False → False) ∨ (p5 → False)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_7
          case inl assump_18 =>
            cases assump_18
            case intro assump_20 assump_21 =>
              apply Or.inl
              intro assump_26
              intro assump_27
              cases assump_26
              case inl assump_30 =>
                have assump_60 : p0 := by
                  exact assump_27
                let assump_38 := assump_9 assump_60
                apply False.elim assump_38
              case inr assump_31 =>
                have assump_61 : p0 := by
                  exact assump_27
                let assump_48 := assump_9 assump_61
                apply False.elim assump_48
          case inr assump_19 =>
            cases assump_19
            case intro assump_52 assump_53 =>
              apply False.elim assump_52
  let assump_4 := assump_1 assump_59
  apply False.elim assump_4


variable (p5 p6 p1 p2 p0 p3 p7 : Prop)
theorem file16_76918 : ((((((p7 ∧ True) ∨ (p1 ∨ p7)) → ((p3 ∨ False) ∨ (False → p2))) ∧ (((p5 ∨ p5) ∧ (p5 → p2)) ∨ ((p0 → False) → (p3 → False)))) ∧ ((((p2 ∨ True) → (False ∧ p6)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_10
          case inl assump_12 =>
            have assump_66 : (((p2 ∨ True) → (False ∧ p6)) → False) := by
              intro assump_21
              have assump_67 : (p2 ∨ True) := by
                apply Or.inr
                apply True.intro
              let assump_24 := assump_21 assump_67
              let assump_25 := And.left assump_24
              apply False.elim assump_25
            let assump_20 := assump_3 assump_66
            apply False.elim assump_20
          case inr assump_13 =>
            have assump_68 : (((p2 ∨ True) → (False ∧ p6)) → False) := by
              intro assump_39
              have assump_69 : (p2 ∨ True) := by
                apply Or.inr
                apply True.intro
              let assump_42 := assump_39 assump_69
              let assump_43 := And.left assump_42
              apply False.elim assump_43
            let assump_38 := assump_3 assump_68
            apply False.elim assump_38
      case inr assump_9 =>
        have assump_70 : (((p2 ∨ True) → (False ∧ p6)) → False) := by
          intro assump_55
          have assump_71 : (p2 ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_58 := assump_55 assump_71
          let assump_59 := And.left assump_58
          apply False.elim assump_59
        let assump_54 := assump_3 assump_70
        apply False.elim assump_54


variable (p4 p1 p0 p7 p3 p6 p5 : Prop)
theorem file16_78817 : (((((p1 ∧ p0) → (False → p4)) ∨ ((False ∨ p1) ∧ (p5 → False))) → False) → ((((p7 ∧ p3) → False) ∨ ((p0 ∨ True) → False)) ∨ (((p4 → False) ∨ (p6 → False)) ∨ ((p3 → p3) → (p6 ∨ p0))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    have assump_21 : (((p1 ∧ p0) → (False → p4)) ∨ ((False ∨ p1) ∧ (p5 → False))) := by
      apply Or.inl
      intro assump_14
      intro assump_15
      apply False.elim assump_15
    let assump_13 := assump_1 assump_21
    apply False.elim assump_13


variable (p6 p3 p0 p2 p7 p5 p1 : Prop)
theorem file16_79439 : ((((((p7 → False) ∧ (p1 → p2)) ∨ ((False ∧ p5) → (True ∨ p1))) → (((p7 ∨ True) ∧ (p2 ∨ p0)) → ((p1 ∧ p2) → (p3 ∧ p6)))) ∧ ((((True ∨ p0) ∧ (p1 ∧ p2)) ∧ ((p2 ∧ False) ∨ (True → False))) ∧ (((False → True) → False) ∧ ((True ∨ False) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_10
          case inl assump_12 =>
            cases assump_11
            case intro assump_16 assump_17 =>
              cases assump_9
              case inl assump_22 =>
                cases assump_22
                case intro assump_24 assump_25 =>
                  apply False.elim assump_25
              case inr assump_23 =>
                cases assump_7
                case intro assump_32 assump_33 =>
                  have assump_70 : (True ∨ False) := by
                    apply Or.inl
                    apply True.intro
                  let assump_38 := assump_33 assump_70
                  apply False.elim assump_38
          case inr assump_13 =>
            cases assump_11
            case intro assump_44 assump_45 =>
              cases assump_9
              case inl assump_50 =>
                cases assump_50
                case intro assump_52 assump_53 =>
                  apply False.elim assump_53
              case inr assump_51 =>
                cases assump_7
                case intro assump_60 assump_61 =>
                  have assump_71 : (True ∨ False) := by
                    apply Or.inl
                    apply True.intro
                  let assump_66 := assump_61 assump_71
                  apply False.elim assump_66


variable (p2 : Prop)
theorem file16_81297 : (((((p2 ∨ True) → False) → ((False → False) → False)) → False) → False) := by
  intro assump_17
  have assump_34 : (((p2 ∨ True) → False) → ((False → False) → False)) := by
    intro assump_21
    intro assump_22
    have assump_35 : (p2 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_27 := assump_21 assump_35
    apply False.elim assump_27
  let assump_20 := assump_17 assump_34
  apply False.elim assump_20


variable (p5 p2 p4 p1 p6 p0 : Prop)
theorem file16_81791 : ((((((p6 → False) ∧ (p1 → False)) → ((p5 → False) → False)) → (((True ∨ False) ∧ (p4 → False)) → False)) ∧ ((((p0 → False) → (p2 → p2)) ∨ ((False → p5) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_18 : (((p0 → False) → (p2 → p2)) ∨ ((False → p5) → False)) := by
      apply Or.inl
      intro assump_9
      intro assump_10
      exact assump_10
    let assump_8 := assump_3 assump_18
    apply False.elim assump_8


variable (p1 p2 p6 : Prop)
theorem file16_82331 : (((((p2 ∧ p6) → False) → ((p1 ∨ p1) → (p1 → True))) → False) → False) := by
  intro assump_1
  have assump_11 : (((p2 ∧ p6) → False) → ((p1 ∨ p1) → (p1 → True))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p2 p1 p3 p6 p7 p0 : Prop)
theorem file16_82702 : ((((((p6 ∨ p1) ∧ (p0 ∨ False)) → ((p1 → p7) → False)) → (((False ∧ p1) ∧ (p7 → False)) → ((p1 → p2) ∨ (p6 → p3)))) → False) → False) := by
  intro assump_1
  have assump_16 : ((((p6 ∨ p1) ∧ (p0 ∨ False)) → ((p1 → p7) → False)) → (((False ∧ p1) ∧ (p7 → False)) → ((p1 → p2) ∨ (p6 → p3)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        apply False.elim assump_9
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p2 p0 p1 p6 p5 p4 p7 p3 : Prop)
theorem file16_83314 : (((((p4 → True) → False) → False) ∧ (((True ∨ p7) → False) → False)) ∨ ((((p1 ∨ p2) ∧ (p3 ∧ p6)) ∨ ((p0 ∧ p7) ∨ (p5 → False))) ∨ (((False → p6) → False) → False))) := by
  apply Or.inl
  apply And.intro
  intro assump_1
  have assump_16 : (p4 → True) := by
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4
  intro assump_9
  have assump_17 : (True ∨ p7) := by
    apply Or.inl
    apply True.intro
  let assump_12 := assump_9 assump_17
  apply False.elim assump_12


variable (p5 p7 p0 p6 p1 p3 p2 : Prop)
theorem file16_83898 : ((((((True → False) ∧ (p1 ∧ p1)) ∧ ((p3 ∨ False) ∧ (p0 → False))) ∨ (((p6 → p1) ∧ (p5 ∨ p2)) ∧ ((True → False) → (True → p5)))) ∧ ((((p6 → False) ∨ (p0 → p0)) → False) ∧ (((p2 ∧ p7) → (p5 → p2)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_9
          case intro assump_12 assump_13 =>
            cases assump_7
            case intro assump_18 assump_19 =>
              cases assump_18
              case inl assump_20 =>
                cases assump_3
                case intro assump_26 assump_27 =>
                  have assump_104 : ((p2 ∧ p7) → (p5 → p2)) := by
                    intro assump_33
                    intro assump_34
                    cases assump_33
                    case intro assump_37 assump_38 =>
                      exact assump_37
                  let assump_32 := assump_27 assump_104
                  apply False.elim assump_32
              case inr assump_21 =>
                apply False.elim assump_21
    case inr assump_5 =>
      cases assump_5
      case intro assump_48 assump_49 =>
        cases assump_48
        case intro assump_50 assump_51 =>
          cases assump_51
          case inl assump_54 =>
            cases assump_3
            case intro assump_60 assump_61 =>
              have assump_105 : ((p2 ∧ p7) → (p5 → p2)) := by
                intro assump_67
                intro assump_68
                cases assump_67
                case intro assump_71 assump_72 =>
                  exact assump_71
              let assump_66 := assump_61 assump_105
              apply False.elim assump_66
          case inr assump_55 =>
            cases assump_3
            case intro assump_84 assump_85 =>
              have assump_106 : ((p2 ∧ p7) → (p5 → p2)) := by
                intro assump_91
                intro assump_92
                cases assump_91
                case intro assump_95 assump_96 =>
                  exact assump_95
              let assump_90 := assump_85 assump_106
              apply False.elim assump_90


variable (p1 p5 p3 p4 p7 p2 p0 p6 : Prop)
theorem file16_86212 : (((((p5 → False) → (p2 → p3)) → False) ∧ (((p2 ∨ True) ∨ (p3 ∧ p0)) → ((p3 ∨ p2) → False))) → ((((p6 → False) ∨ (p0 ∧ p2)) → ((p6 → False) ∨ (p1 ∨ p6))) → (((p7 ∨ p4) ∧ (p5 ∨ p4)) → ((p2 ∧ p4) → False)))) := by
  intro assump_5
  intro assump_6
  intro assump_7
  intro assump_8
  cases assump_8
  case intro assump_9 assump_10 =>
    cases assump_7
    case intro assump_15 assump_16 =>
      cases assump_15
      case inl assump_17 =>
        cases assump_16
        case inl assump_21 =>
          cases assump_5
          case intro assump_27 assump_28 =>
            have assump_87 : ((p2 ∨ True) ∨ (p3 ∧ p0)) := by
              apply Or.inl
              apply Or.inl
              exact assump_9
            let assump_33 := assump_28 assump_87
            have assump_88 : (p3 ∨ p2) := by
              apply Or.inr
              exact assump_9
            let assump_34 := assump_33 assump_88
            apply False.elim assump_34
        case inr assump_22 =>
          cases assump_5
          case intro assump_42 assump_43 =>
            have assump_89 : ((p2 ∨ True) ∨ (p3 ∧ p0)) := by
              apply Or.inl
              apply Or.inl
              exact assump_9
            let assump_48 := assump_43 assump_89
            have assump_90 : (p3 ∨ p2) := by
              apply Or.inr
              exact assump_9
            let assump_49 := assump_48 assump_90
            apply False.elim assump_49
      case inr assump_18 =>
        cases assump_16
        case inl assump_55 =>
          cases assump_5
          case intro assump_61 assump_62 =>
            have assump_91 : ((p2 ∨ True) ∨ (p3 ∧ p0)) := by
              apply Or.inl
              apply Or.inl
              exact assump_9
            let assump_67 := assump_62 assump_91
            have assump_92 : (p3 ∨ p2) := by
              apply Or.inr
              exact assump_9
            let assump_68 := assump_67 assump_92
            apply False.elim assump_68
        case inr assump_56 =>
          cases assump_5
          case intro assump_76 assump_77 =>
            have assump_93 : ((p2 ∨ True) ∨ (p3 ∧ p0)) := by
              apply Or.inl
              apply Or.inl
              exact assump_9
            let assump_82 := assump_77 assump_93
            have assump_94 : (p3 ∨ p2) := by
              apply Or.inr
              exact assump_9
            let assump_83 := assump_82 assump_94
            apply False.elim assump_83


variable (p7 p2 p6 p5 p1 : Prop)
theorem file16_88707 : (((((False ∧ p6) ∧ (p7 → True)) ∨ ((False → False) ∧ (False → False))) → False) → ((((p2 → p1) ∧ (p5 ∨ True)) ∨ ((p7 ∧ p2) → False)) ∨ (((False → p7) ∨ (p5 ∧ p7)) → ((p2 ∧ p1) → False)))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply And.intro
  intro assump_4
  have assump_18 : (((False ∧ p6) ∧ (p7 → True)) ∨ ((False → False) ∧ (False → False))) := by
    apply Or.inr
    apply And.intro
    intro assump_9
    apply False.elim assump_9
    intro assump_12
    apply False.elim assump_12
  let assump_8 := assump_1 assump_18
  apply False.elim assump_8
  apply Or.inr
  apply True.intro


variable (p0 p1 p4 p6 p7 p3 p5 p2 : Prop)
theorem file16_89379 : ((((((p3 ∧ p7) → False) ∨ ((True → p6) → False)) ∧ (((p0 → p3) → (p4 → False)) ∧ ((False ∨ False) ∧ (p3 ∨ p6)))) ∧ ((((p2 ∨ p1) ∨ (p2 → p2)) ∧ ((p5 ∨ p3) → (False → False))) ∧ (((p1 ∧ True) ∧ (p7 → False)) ∧ ((p2 → p6) → (False → p2))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_5
        case intro assump_10 assump_11 =>
          cases assump_11
          case intro assump_14 assump_15 =>
            cases assump_14
            case inl assump_16 =>
              apply False.elim assump_16
            case inr assump_17 =>
              apply False.elim assump_17
      case inr assump_7 =>
        cases assump_5
        case intro assump_24 assump_25 =>
          cases assump_25
          case intro assump_28 assump_29 =>
            cases assump_28
            case inl assump_30 =>
              apply False.elim assump_30
            case inr assump_31 =>
              apply False.elim assump_31


variable (p0 p7 p5 p6 p4 : Prop)
theorem file16_90513 : ((((((p5 → p7) ∧ (p4 → False)) → False) ∧ (((p0 → p0) ∧ (p5 ∧ True)) ∧ ((p7 → False) ∧ (False → p6)))) ∧ ((((False → False) → False) → ((p0 → False) → (False → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_11
          case intro assump_14 assump_15 =>
            cases assump_9
            case intro assump_20 assump_21 =>
              have assump_37 : (((False → False) → False) → ((p0 → False) → (False → False))) := by
                intro assump_29
                intro assump_30
                intro assump_31
                apply False.elim assump_31
              let assump_28 := assump_3 assump_37
              apply False.elim assump_28


variable (p2 p3 p5 p7 : Prop)
theorem file16_91481 : (((((p3 ∧ p2) ∨ (p5 → True)) ∨ ((p7 ∧ False) ∧ (p7 → False))) → False) → False) := by
  intro assump_1
  have assump_9 : (((p3 ∧ p2) ∨ (p5 → True)) ∨ ((p7 ∧ False) ∧ (p7 → False))) := by
    apply Or.inl
    apply Or.inr
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_9
  apply False.elim assump_4


variable (p3 p1 p6 p7 p0 p5 p2 : Prop)
theorem file16_91869 : ((((((p0 ∧ True) → False) ∧ ((False ∨ False) ∧ (p6 → p5))) ∧ (((p0 → p3) ∧ (p1 → p3)) → ((p3 ∧ p3) ∧ (p1 ∨ p1)))) ∧ ((((p1 ∨ p7) ∧ (p2 ∧ p7)) ∨ ((p5 ∨ p5) → False)) → False)) → False) := by
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
            apply False.elim assump_12
          case inr assump_13 =>
            apply False.elim assump_13


variable (p3 p6 p7 p2 : Prop)
theorem file16_92528 : (((((p3 → False) → (p2 → p6)) → ((p6 ∧ False) → (p7 → False))) → False) → False) := by
  intro assump_1
  have assump_19 : (((p3 → False) → (p2 → p6)) → ((p6 ∧ False) → (p7 → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      apply False.elim assump_11
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p7 p3 p2 p6 p5 : Prop)
theorem file16_92987 : (((((p2 ∧ p3) → (p7 → p3)) → False) ∧ (((p6 ∧ p7) → False) ∧ ((p5 → p3) ∨ (p7 → False)))) → False) := by
  intro assump_6
  cases assump_6
  case intro assump_7 assump_8 =>
    cases assump_8
    case intro assump_11 assump_12 =>
      cases assump_12
      case inl assump_15 =>
        have assump_53 : ((p2 ∧ p3) → (p7 → p3)) := by
          intro assump_22
          intro assump_23
          cases assump_22
          case intro assump_26 assump_27 =>
            exact assump_27
        let assump_21 := assump_7 assump_53
        apply False.elim assump_21
      case inr assump_16 =>
        have assump_54 : ((p2 ∧ p3) → (p7 → p3)) := by
          intro assump_40
          intro assump_41
          cases assump_40
          case intro assump_44 assump_45 =>
            exact assump_45
        let assump_39 := assump_7 assump_54
        apply False.elim assump_39


variable (p1 p5 p6 p3 : Prop)
theorem file16_93917 : ((((((False → False) ∨ (False ∧ p6)) → False) → (((True → p3) → (True → False)) ∧ ((p3 ∨ p1) ∧ (p5 → False)))) → False) → False) := by
  intro assump_1
  have assump_45 : ((((False → False) ∨ (False ∧ p6)) → False) → (((True → p3) → (True → False)) ∧ ((p3 ∨ p1) ∧ (p5 → False)))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    intro assump_7
    have assump_46 : ((False → False) ∨ (False ∧ p6)) := by
      apply Or.inl
      intro assump_15
      apply False.elim assump_15
    let assump_14 := assump_5 assump_46
    apply False.elim assump_14
    apply And.intro
    have assump_47 : ((False → False) ∨ (False ∧ p6)) := by
      apply Or.inl
      intro assump_24
      apply False.elim assump_24
    let assump_23 := assump_5 assump_47
    apply False.elim assump_23
    intro assump_30
    have assump_48 : ((False → False) ∨ (False ∧ p6)) := by
      apply Or.inl
      intro assump_36
      apply False.elim assump_36
    let assump_35 := assump_5 assump_48
    apply False.elim assump_35
  let assump_4 := assump_1 assump_45
  apply False.elim assump_4


variable (p6 p7 p2 p3 p1 p0 p4 p5 : Prop)
theorem file16_95066 : (((((p7 ∧ False) ∧ (p3 ∧ False)) → ((p4 → p2) ∧ (True → p5))) ∨ (((p3 → p0) ∧ (p3 → p4)) → False)) ∨ ((((p2 → p2) → (p4 ∧ p4)) ∧ ((p1 → p4) ∨ (p4 → p4))) → (((p6 → False) → (p3 ∨ p1)) ∧ ((p4 → False) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      apply False.elim assump_8
  intro assump_13
  cases assump_1
  case intro assump_16 assump_17 =>
    cases assump_16
    case intro assump_18 assump_19 =>
      apply False.elim assump_19


variable (p0 p3 p4 p5 p6 p7 : Prop)
theorem file16_95726 : (((((p4 → p4) → False) ∧ ((False → False) → False)) → False) ∨ ((((p0 → True) → False) → ((p7 ∨ p7) → False)) → (((p5 ∧ p4) ∧ (p3 → p5)) ∧ ((p6 → False) → (p0 → False))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : (False → False) := by
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p4 p0 p5 p6 p1 p2 : Prop)
theorem file16_96212 : (((((p6 ∨ p5) → False) → ((True → False) ∧ (p1 → p4))) ∧ (((p2 → False) ∧ (False ∧ p5)) ∧ ((p1 → p0) ∧ (True ∨ False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          apply False.elim assump_12


variable (p7 p3 p2 p4 p6 p5 p0 : Prop)
theorem file16_96695 : (((((p0 → p6) ∧ (p5 → p0)) → ((p4 → False) ∨ (p3 → False))) ∨ (((p7 ∨ p5) → (p3 ∨ p3)) → False)) → ((((True → False) ∧ (p5 ∨ False)) → ((p3 ∧ p2) → False)) ∨ (((p3 → False) → False) ∨ ((p6 → False) → False)))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    intro assump_7
    cases assump_7
    case intro assump_8 assump_9 =>
      cases assump_6
      case intro assump_14 assump_15 =>
        cases assump_15
        case inl assump_18 =>
          have assump_54 : True := by
            apply True.intro
          let assump_23 := assump_14 assump_54
          apply False.elim assump_23
        case inr assump_19 =>
          apply False.elim assump_19
  case inr assump_3 =>
    apply Or.inl
    intro assump_31
    intro assump_32
    cases assump_32
    case intro assump_33 assump_34 =>
      cases assump_31
      case intro assump_39 assump_40 =>
        cases assump_40
        case inl assump_43 =>
          have assump_55 : True := by
            apply True.intro
          let assump_48 := assump_39 assump_55
          apply False.elim assump_48
        case inr assump_44 =>
          apply False.elim assump_44


variable (p7 p1 p4 p6 p5 p3 p0 : Prop)
theorem file16_97946 : (((((p0 → p7) → (p7 → p1)) ∨ ((p7 → False) ∧ (p3 ∧ p0))) → False) → ((((p4 → False) ∨ (p5 ∧ True)) → ((p7 ∧ p1) → False)) ∨ (((p5 → p6) ∧ (p5 → p3)) → ((p3 → False) → False)))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_4
    case inl assump_12 =>
      have assump_48 : (((p0 → p7) → (p7 → p1)) ∨ ((p7 → False) ∧ (p3 ∧ p0))) := by
        apply Or.inl
        intro assump_20
        intro assump_21
        exact assump_7
      let assump_19 := assump_1 assump_48
      apply False.elim assump_19
    case inr assump_13 =>
      cases assump_13
      case intro assump_29 assump_30 =>
        have assump_49 : (((p0 → p7) → (p7 → p1)) ∨ ((p7 → False) ∧ (p3 ∧ p0))) := by
          apply Or.inl
          intro assump_39
          intro assump_40
          exact assump_7
        let assump_38 := assump_1 assump_49
        apply False.elim assump_38


variable (p5 p7 p3 p0 p4 p6 : Prop)
theorem file16_98955 : (((((p3 ∧ False) ∧ (p0 → True)) ∧ ((p7 → True) → (p7 ∧ p6))) → (((p6 → False) → (p4 → True)) → ((p4 ∨ True) → False))) ∨ ((((p3 → True) ∧ (True → False)) ∨ ((p5 → False) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_1
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_12
        case intro assump_14 assump_15 =>
          apply False.elim assump_15
  case inr assump_5 =>
    cases assump_1
    case intro assump_24 assump_25 =>
      cases assump_24
      case intro assump_26 assump_27 =>
        cases assump_26
        case intro assump_28 assump_29 =>
          apply False.elim assump_29


variable (p1 p3 p2 p7 p6 : Prop)
theorem file16_99781 : (((((True ∨ p6) → (True ∧ p7)) ∧ ((False → p6) → False)) → False) ∨ ((((p1 ∧ p2) → (p3 ∧ p7)) → ((p1 → False) ∨ (False → True))) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : (False → p6) := by
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p0 p1 p3 p2 p6 p4 : Prop)
theorem file16_100231 : ((((((p2 ∧ False) ∧ (p1 ∧ p4)) → ((p4 → p0) ∧ (p3 → False))) ∨ (((True → p2) → False) ∧ ((p1 ∧ p2) ∧ (p6 → p3)))) → False) → False) := by
  intro assump_1
  have assump_31 : ((((p2 ∧ False) ∧ (p1 ∧ p4)) → ((p4 → p0) ∧ (p3 → False))) ∨ (((True → p2) → False) ∧ ((p1 ∧ p2) ∧ (p6 → p3)))) := by
    apply Or.inl
    intro assump_5
    apply And.intro
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        apply False.elim assump_12
    intro assump_17
    cases assump_5
    case intro assump_20 assump_21 =>
      cases assump_20
      case intro assump_22 assump_23 =>
        apply False.elim assump_23
  let assump_4 := assump_1 assump_31
  apply False.elim assump_4


variable (p1 p7 p5 p6 p3 p4 : Prop)
theorem file16_101049 : (((((p1 → False) ∧ (p5 → False)) ∧ ((p1 ∨ p5) ∧ (p5 → False))) ∨ (((p5 ∧ p7) ∧ (p3 → False)) ∨ ((p1 ∨ p6) → (p7 → False)))) → ((((False ∧ p1) ∧ (p4 → False)) ∧ ((p7 ∧ p6) → False)) → False)) := by
  intro assump_5
  intro assump_6
  cases assump_6
  case intro assump_7 assump_8 =>
    cases assump_7
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        apply False.elim assump_11


variable (p6 p5 p2 p3 p1 p7 : Prop)
theorem file16_101543 : ((((((p7 → False) ∧ (p3 → False)) → ((p7 ∨ p5) ∨ (p5 → False))) ∨ (((p1 → False) → False) ∨ ((p6 ∧ p2) → (p3 → p3)))) → False) → False) := by
  intro assump_5
  have assump_36 : ((((p7 → False) ∧ (p3 → False)) → ((p7 ∨ p5) ∨ (p5 → False))) ∨ (((p1 → False) → False) ∨ ((p6 ∧ p2) → (p3 → p3)))) := by
    apply Or.inl
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      apply Or.inr
      intro assump_16
      have assump_37 : ((((p7 → False) ∧ (p3 → False)) → ((p7 ∨ p5) ∨ (p5 → False))) ∨ (((p1 → False) → False) ∨ ((p6 ∧ p2) → (p3 → p3)))) := by
        apply Or.inl
        intro assump_23
        cases assump_23
        case intro assump_24 assump_25 =>
          apply Or.inl
          apply Or.inr
          exact assump_16
      let assump_22 := assump_5 assump_37
      apply False.elim assump_22
  let assump_8 := assump_5 assump_36
  apply False.elim assump_8


variable (p7 p6 p4 p3 p1 p5 : Prop)
theorem file16_102505 : ((((((False → False) ∧ (p4 ∨ p5)) ∨ ((p1 → False) ∨ (p4 ∨ p7))) → (((p4 → False) → (p7 → False)) → ((p1 ∨ True) ∨ (p3 → p6)))) → False) → False) := by
  intro assump_18
  have assump_51 : ((((False → False) ∧ (p4 ∨ p5)) ∨ ((p1 → False) ∨ (p4 ∨ p7))) → (((p4 → False) → (p7 → False)) → ((p1 ∨ True) ∨ (p3 → p6)))) := by
    intro assump_22
    intro assump_23
    cases assump_22
    case inl assump_26 =>
      cases assump_26
      case intro assump_28 assump_29 =>
        cases assump_29
        case inl assump_32 =>
          apply Or.inl
          apply Or.inr
          apply True.intro
        case inr assump_33 =>
          apply Or.inl
          apply Or.inr
          apply True.intro
    case inr assump_27 =>
      cases assump_27
      case inl assump_38 =>
        apply Or.inl
        apply Or.inr
        apply True.intro
      case inr assump_39 =>
        cases assump_39
        case inl assump_42 =>
          apply Or.inl
          apply Or.inr
          apply True.intro
        case inr assump_43 =>
          apply Or.inl
          apply Or.inr
          apply True.intro
  let assump_21 := assump_18 assump_51
  apply False.elim assump_21


variable (p5 p0 p4 p6 p7 p2 : Prop)
theorem file16_103731 : (((((p6 ∨ p4) → False) ∧ ((p2 ∧ False) → (p7 → p2))) → (((p2 → p2) → False) → ((p7 → p6) ∧ (True → p0)))) ∨ ((((p5 → p6) → False) ∨ ((p6 → False) ∧ (False → p2))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  cases assump_1
  case intro assump_8 assump_9 =>
    have assump_43 : (p2 → p2) := by
      intro assump_17
      exact assump_17
    let assump_16 := assump_2 assump_43
    apply False.elim assump_16
  intro assump_23
  cases assump_1
  case intro assump_28 assump_29 =>
    have assump_44 : (p2 → p2) := by
      intro assump_37
      exact assump_37
    let assump_36 := assump_2 assump_44
    apply False.elim assump_36


