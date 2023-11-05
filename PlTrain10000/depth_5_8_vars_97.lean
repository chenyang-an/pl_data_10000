variable (p5 p1 p4 p0 p3 p6 p7 p2 : Prop)
theorem file97_50 : (((((p1 ∧ True) ∨ (p5 ∨ p2)) → False) ∧ (((p3 → False) ∧ (p0 ∧ False)) ∧ ((p2 → p6) ∨ (p0 ∨ p5)))) → ((((p0 ∧ p4) ∧ (p2 → False)) ∧ ((p7 ∨ p3) ∨ (p2 ∧ False))) ∧ (((p3 → p2) ∧ (p1 → False)) ∧ ((p0 ∨ p7) ∨ (p7 ∧ False))))) := by
  intro assump_16
  apply And.intro
  apply And.intro
  apply And.intro
  apply And.intro
  cases assump_16
  case intro assump_17 assump_18 =>
    cases assump_18
    case intro assump_21 assump_22 =>
      cases assump_21
      case intro assump_23 assump_24 =>
        cases assump_24
        case intro assump_27 assump_28 =>
          apply False.elim assump_28
  cases assump_16
  case intro assump_33 assump_34 =>
    cases assump_34
    case intro assump_37 assump_38 =>
      cases assump_37
      case intro assump_39 assump_40 =>
        cases assump_40
        case intro assump_43 assump_44 =>
          apply False.elim assump_44
  intro assump_49
  cases assump_16
  case intro assump_52 assump_53 =>
    cases assump_53
    case intro assump_56 assump_57 =>
      cases assump_56
      case intro assump_58 assump_59 =>
        cases assump_59
        case intro assump_62 assump_63 =>
          apply False.elim assump_63
  cases assump_16
  case intro assump_68 assump_69 =>
    cases assump_69
    case intro assump_72 assump_73 =>
      cases assump_72
      case intro assump_74 assump_75 =>
        cases assump_75
        case intro assump_78 assump_79 =>
          apply False.elim assump_79
  apply And.intro
  apply And.intro
  intro assump_84
  cases assump_16
  case intro assump_87 assump_88 =>
    cases assump_88
    case intro assump_91 assump_92 =>
      cases assump_91
      case intro assump_93 assump_94 =>
        cases assump_94
        case intro assump_97 assump_98 =>
          apply False.elim assump_98
  intro assump_103
  cases assump_16
  case intro assump_106 assump_107 =>
    cases assump_107
    case intro assump_110 assump_111 =>
      cases assump_110
      case intro assump_112 assump_113 =>
        cases assump_113
        case intro assump_116 assump_117 =>
          apply False.elim assump_117
  cases assump_16
  case intro assump_122 assump_123 =>
    cases assump_123
    case intro assump_126 assump_127 =>
      cases assump_126
      case intro assump_128 assump_129 =>
        cases assump_129
        case intro assump_132 assump_133 =>
          apply False.elim assump_133


variable (p7 p5 p1 p6 p2 p3 p4 p0 : Prop)
theorem file97_2488 : ((((((p3 → False) → False) → ((p5 → p3) → (p7 → p4))) ∧ (((p6 → False) → (p2 → p4)) ∧ ((p5 → p7) → False))) ∧ ((((p2 → p7) ∧ (p6 ∧ p2)) ∧ ((p2 ∧ p1) → (p2 → False))) ∧ (((p2 ∧ p6) → (p0 ∧ False)) ∧ ((False → p0) → (False ∧ p7))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_3
        case intro assump_14 assump_15 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              cases assump_19
              case intro assump_22 assump_23 =>
                cases assump_15
                case intro assump_30 assump_31 =>
                  have assump_44 : (False → p0) := by
                    intro assump_37
                    apply False.elim assump_37
                  let assump_36 := assump_31 assump_44
                  let assump_40 := And.left assump_36
                  apply False.elim assump_40


variable (p3 p1 p2 p6 p7 p5 : Prop)
theorem file97_3636 : ((((((p1 → False) ∨ (p2 → p2)) → ((p7 ∨ p7) → (p7 → False))) ∧ (((p1 → False) → False) → ((p2 ∧ p2) → (p3 → False)))) ∧ ((((p6 → False) → False) → ((p6 ∨ p2) ∨ (p5 → True))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_20 : (((p6 → False) → False) → ((p6 ∨ p2) ∨ (p5 → True))) := by
        intro assump_13
        apply Or.inr
        intro assump_16
        apply True.intro
      let assump_12 := assump_3 assump_20
      apply False.elim assump_12


variable (p3 p0 p1 p4 p7 p5 p2 : Prop)
theorem file97_4272 : (((((p5 → p1) ∧ (p3 ∨ p1)) ∧ ((False ∧ p1) ∨ (p1 ∧ p1))) → (((p0 ∨ p5) ∨ (p1 ∨ p2)) ∨ ((True ∧ p3) ∧ (p0 ∨ p2)))) ∨ ((((p5 → p2) → (p7 → p3)) → False) ∨ (((p3 → p4) ∨ (True → p2)) → ((True ∨ True) ∧ (p7 ∧ p4))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        cases assump_3
        case inl assump_12 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            apply False.elim assump_14
        case inr assump_13 =>
          cases assump_13
          case intro assump_18 assump_19 =>
            apply Or.inl
            apply Or.inr
            apply Or.inl
            exact assump_19
      case inr assump_9 =>
        cases assump_3
        case inl assump_26 =>
          cases assump_26
          case intro assump_28 assump_29 =>
            apply False.elim assump_28
        case inr assump_27 =>
          cases assump_27
          case intro assump_32 assump_33 =>
            apply Or.inl
            apply Or.inr
            apply Or.inl
            exact assump_33


variable (p2 p6 p3 p5 p0 p7 p1 : Prop)
theorem file97_5497 : ((((((False ∧ p2) ∧ (True ∧ p6)) ∧ ((p0 ∨ p7) → False)) ∧ (((False ∨ p0) ∧ (p0 → False)) → False)) ∧ ((((True → p3) ∧ (p5 ∧ p5)) ∨ ((p0 → False) → False)) ∨ (((True → p2) → (p2 → False)) ∧ ((p1 → p1) → False)))) → False) := by
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
            apply False.elim assump_10


variable (p7 p6 p5 : Prop)
theorem file97_6128 : ((((((p6 ∨ p7) → False) → ((p7 → False) ∧ (p5 → False))) → (((False → False) ∨ (False ∨ p6)) → ((False ∧ p7) ∧ (p7 → False)))) ∧ ((((p6 ∨ True) → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : (((p6 ∨ True) → False) → False) := by
      intro assump_9
      have assump_20 : (p6 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_12 := assump_9 assump_20
      apply False.elim assump_12
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


variable (p3 p2 p5 p0 : Prop)
theorem file97_6748 : (((((True ∨ True) ∨ (p3 → p5)) → False) → (((p0 → p0) → False) → ((p0 ∧ p2) → (False → False)))) ∧ ((((True → False) → False) → False) → False)) := by
  apply And.intro
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  apply False.elim assump_4
  intro assump_7
  have assump_21 : ((True → False) → False) := by
    intro assump_11
    have assump_22 : True := by
      apply True.intro
    let assump_14 := assump_11 assump_22
    apply False.elim assump_14
  let assump_10 := assump_7 assump_21
  apply False.elim assump_10


variable (p7 p3 p2 p1 p0 p4 : Prop)
theorem file97_7354 : (((((p4 → p1) → (False → False)) ∧ ((True ∨ True) ∧ (False ∧ p0))) ∨ (((p3 → False) → False) → ((p2 → False) → (False → False)))) ∨ ((((p7 ∧ True) → False) ∨ ((p3 → p7) → (p3 → p3))) → (((False → False) ∨ (False → False)) ∨ ((p3 → p2) ∨ (p4 → False))))) := by
  apply Or.inl
  apply Or.inr
  intro assump_20
  intro assump_21
  intro assump_22
  apply False.elim assump_22


variable (p5 p1 p7 p6 p3 p4 p0 : Prop)
theorem file97_7790 : (((((True → False) → (True ∧ p5)) ∧ ((p1 ∧ p3) ∧ (p5 → False))) ∧ (((p6 ∧ False) ∧ (False → False)) ∨ ((False → False) ∧ (True → p4)))) ∨ ((((p5 ∨ p0) ∧ (p3 ∨ p7)) ∨ ((p5 ∧ False) → False)) ∨ (((p7 ∨ p3) → False) → False))) := by
  apply Or.inr
  apply Or.inl
  apply Or.inr
  intro assump_8
  cases assump_8
  case intro assump_9 assump_10 =>
    apply False.elim assump_10


variable (p5 p7 p1 p6 p0 p3 p2 p4 : Prop)
theorem file97_8231 : (((((p7 → p4) ∧ (p0 ∧ False)) → False) → False) → ((((p6 → False) ∨ (p4 ∨ p6)) ∧ ((True ∧ p6) ∨ (p7 ∧ p4))) ∧ (((p1 ∧ p4) ∧ (False → p3)) ∧ ((True ∨ p2) → (p5 → False))))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  apply Or.inl
  intro assump_4
  have assump_121 : (((p7 → p4) ∧ (p0 ∧ False)) → False) := by
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      cases assump_11
      case intro assump_14 assump_15 =>
        apply False.elim assump_15
  let assump_8 := assump_1 assump_121
  apply False.elim assump_8
  have assump_122 : (((p7 → p4) ∧ (p0 ∧ False)) → False) := by
    intro assump_26
    cases assump_26
    case intro assump_27 assump_28 =>
      cases assump_28
      case intro assump_31 assump_32 =>
        apply False.elim assump_32
  let assump_25 := assump_1 assump_122
  apply False.elim assump_25
  apply And.intro
  apply And.intro
  apply And.intro
  have assump_123 : (((p7 → p4) ∧ (p0 ∧ False)) → False) := by
    intro assump_43
    cases assump_43
    case intro assump_44 assump_45 =>
      cases assump_45
      case intro assump_48 assump_49 =>
        apply False.elim assump_49
  let assump_42 := assump_1 assump_123
  apply False.elim assump_42
  have assump_124 : (((p7 → p4) ∧ (p0 ∧ False)) → False) := by
    intro assump_60
    cases assump_60
    case intro assump_61 assump_62 =>
      cases assump_62
      case intro assump_65 assump_66 =>
        apply False.elim assump_66
  let assump_59 := assump_1 assump_124
  apply False.elim assump_59
  intro assump_74
  apply False.elim assump_74
  intro assump_77
  intro assump_78
  cases assump_77
  case inl assump_81 =>
    have assump_125 : (((p7 → p4) ∧ (p0 ∧ False)) → False) := by
      intro assump_88
      cases assump_88
      case intro assump_89 assump_90 =>
        cases assump_90
        case intro assump_93 assump_94 =>
          apply False.elim assump_94
    let assump_87 := assump_1 assump_125
    apply False.elim assump_87
  case inr assump_82 =>
    have assump_126 : (((p7 → p4) ∧ (p0 ∧ False)) → False) := by
      intro assump_107
      cases assump_107
      case intro assump_108 assump_109 =>
        cases assump_109
        case intro assump_112 assump_113 =>
          apply False.elim assump_113
    let assump_106 := assump_1 assump_126
    apply False.elim assump_106


variable (p5 p3 p7 p1 p4 p6 p2 p0 : Prop)
theorem file97_10641 : ((((((p3 ∨ p0) ∧ (p2 → p3)) ∨ ((False → p0) ∧ (p7 → False))) → (((p5 ∨ p1) ∨ (p0 ∧ p7)) ∨ ((p7 ∧ p1) ∨ (p4 → p1)))) ∧ ((((p1 ∧ p6) ∨ (p4 ∧ p1)) → ((p2 ∧ p1) ∧ (p7 ∨ p7))) ∧ (((False → p6) → False) ∧ ((p4 ∧ True) → (p5 ∨ p0))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        have assump_24 : (False → p6) := by
          intro assump_18
          apply False.elim assump_18
        let assump_17 := assump_10 assump_24
        apply False.elim assump_17


variable (p0 p6 p5 p1 p7 p2 p3 p4 : Prop)
theorem file97_11321 : (((((p5 ∨ p1) → False) → ((True ∨ p4) ∨ (False → False))) ∨ (((p3 ∧ p2) → False) → ((p5 ∨ False) → (False ∨ p6)))) ∨ ((((p1 ∧ False) ∨ (p5 ∧ p4)) ∨ ((p5 → False) ∧ (p3 → p7))) → (((p4 → p0) → (p3 ∧ p0)) ∧ ((p0 ∨ p6) → (p3 → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply True.intro


variable (p3 p5 p6 p1 p2 p4 : Prop)
theorem file97_11718 : (((((p2 ∨ True) ∨ (False → False)) ∨ ((p5 ∨ p1) → (p4 ∨ p2))) → False) → ((((p5 → False) ∨ (p6 ∧ False)) → False) → (((True → False) → False) ∧ ((p3 ∨ p3) → False)))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  have assump_37 : (((p2 ∨ True) ∨ (False → False)) ∨ ((p5 ∨ p1) → (p4 ∨ p2))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_10 := assump_1 assump_37
  apply False.elim assump_10
  intro assump_14
  cases assump_14
  case inl assump_15 =>
    have assump_38 : (((p2 ∨ True) ∨ (False → False)) ∨ ((p5 ∨ p1) → (p4 ∨ p2))) := by
      apply Or.inl
      apply Or.inl
      apply Or.inr
      apply True.intro
    let assump_23 := assump_1 assump_38
    apply False.elim assump_23
  case inr assump_16 =>
    have assump_39 : (((p2 ∨ True) ∨ (False → False)) ∨ ((p5 ∨ p1) → (p4 ∨ p2))) := by
      apply Or.inl
      apply Or.inl
      apply Or.inr
      apply True.intro
    let assump_33 := assump_1 assump_39
    apply False.elim assump_33


variable (p3 p5 p0 p7 p2 : Prop)
theorem file97_12801 : ((((((False ∧ p3) ∨ (True → False)) → False) → (((p3 ∨ p2) ∧ (True → False)) → ((p7 ∨ p5) ∨ (False → p0)))) → False) → False) := by
  intro assump_1
  have assump_32 : ((((False ∧ p3) ∨ (True → False)) → False) → (((p3 ∨ p2) ∧ (True → False)) → ((p7 ∨ p5) ∨ (False → p0)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        apply Or.inr
        intro assump_17
        apply False.elim assump_17
      case inr assump_10 =>
        apply Or.inr
        intro assump_26
        apply False.elim assump_26
  let assump_4 := assump_1 assump_32
  apply False.elim assump_4


variable (p7 p3 p5 p0 p6 p1 p2 : Prop)
theorem file97_13538 : (((((False ∧ p0) ∧ (p5 ∧ p1)) ∨ ((p0 → False) ∧ (p7 → False))) ∧ (((p2 ∨ p0) → (False ∨ p6)) ∧ ((p5 ∨ p3) ∧ (p6 ∧ False)))) → ((((p5 ∧ p5) ∨ (p0 → p5)) ∨ ((p0 → False) → False)) ∨ (((p7 → False) ∧ (p2 → p3)) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          apply False.elim assump_8
    case inr assump_5 =>
      cases assump_5
      case intro assump_12 assump_13 =>
        cases assump_3
        case intro assump_18 assump_19 =>
          cases assump_19
          case intro assump_22 assump_23 =>
            cases assump_22
            case inl assump_24 =>
              cases assump_23
              case intro assump_28 assump_29 =>
                apply False.elim assump_29
            case inr assump_25 =>
              cases assump_23
              case intro assump_36 assump_37 =>
                apply False.elim assump_37


variable (p1 p5 p7 p3 p6 : Prop)
theorem file97_14649 : (((((True ∧ p5) → False) → ((p6 ∨ p6) → (p6 ∨ p1))) → False) → ((((p3 ∧ p1) → False) → False) → (((p7 ∧ True) ∨ (p7 → p6)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_4
    case intro assump_6 assump_7 =>
      have assump_54 : (((True ∧ p5) → False) → ((p6 ∨ p6) → (p6 ∨ p1))) := by
        intro assump_17
        intro assump_18
        cases assump_18
        case inl assump_19 =>
          apply Or.inl
          exact assump_19
        case inr assump_20 =>
          apply Or.inl
          exact assump_20
      let assump_16 := assump_1 assump_54
      apply False.elim assump_16
  case inr assump_5 =>
    have assump_55 : (((True ∧ p5) → False) → ((p6 ∨ p6) → (p6 ∨ p1))) := by
      intro assump_39
      intro assump_40
      cases assump_40
      case inl assump_41 =>
        apply Or.inl
        exact assump_41
      case inr assump_42 =>
        apply Or.inl
        exact assump_42
    let assump_38 := assump_1 assump_55
    apply False.elim assump_38


variable (p7 p0 p2 p3 p6 : Prop)
theorem file97_15759 : ((((((p6 → False) ∨ (True → False)) ∨ ((p3 ∧ p0) ∧ (p6 ∨ True))) ∧ (((p3 ∨ p7) → False) ∨ ((p2 ∨ p2) ∨ (False ∨ p2)))) ∧ ((((p0 ∨ p6) → (p2 ∨ True)) ∨ ((p6 → True) → False)) → False)) → False) := by
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
            have assump_308 : (((p0 ∨ p6) → (p2 ∨ True)) ∨ ((p6 → True) → False)) := by
              apply Or.inl
              intro assump_19
              cases assump_19
              case inl assump_20 =>
                apply Or.inr
                apply True.intro
              case inr assump_21 =>
                apply Or.inr
                apply True.intro
            let assump_18 := assump_3 assump_308
            apply False.elim assump_18
          case inr assump_13 =>
            cases assump_13
            case inl assump_29 =>
              cases assump_29
              case inl assump_31 =>
                have assump_309 : (((p0 ∨ p6) → (p2 ∨ True)) ∨ ((p6 → True) → False)) := by
                  apply Or.inl
                  intro assump_38
                  cases assump_38
                  case inl assump_39 =>
                    apply Or.inl
                    exact assump_31
                  case inr assump_40 =>
                    apply Or.inl
                    exact assump_31
                let assump_37 := assump_3 assump_309
                apply False.elim assump_37
              case inr assump_32 =>
                have assump_310 : (((p0 ∨ p6) → (p2 ∨ True)) ∨ ((p6 → True) → False)) := by
                  apply Or.inl
                  intro assump_53
                  cases assump_53
                  case inl assump_54 =>
                    apply Or.inl
                    exact assump_32
                  case inr assump_55 =>
                    apply Or.inl
                    exact assump_32
                let assump_52 := assump_3 assump_310
                apply False.elim assump_52
            case inr assump_30 =>
              cases assump_30
              case inl assump_63 =>
                apply False.elim assump_63
              case inr assump_64 =>
                have assump_311 : (((p0 ∨ p6) → (p2 ∨ True)) ∨ ((p6 → True) → False)) := by
                  apply Or.inl
                  intro assump_72
                  cases assump_72
                  case inl assump_73 =>
                    apply Or.inl
                    exact assump_64
                  case inr assump_74 =>
                    apply Or.inl
                    exact assump_64
                let assump_71 := assump_3 assump_311
                apply False.elim assump_71
        case inr assump_9 =>
          cases assump_5
          case inl assump_84 =>
            have assump_312 : (((p0 ∨ p6) → (p2 ∨ True)) ∨ ((p6 → True) → False)) := by
              apply Or.inl
              intro assump_91
              cases assump_91
              case inl assump_92 =>
                apply Or.inr
                apply True.intro
              case inr assump_93 =>
                apply Or.inr
                apply True.intro
            let assump_90 := assump_3 assump_312
            apply False.elim assump_90
          case inr assump_85 =>
            cases assump_85
            case inl assump_101 =>
              cases assump_101
              case inl assump_103 =>
                have assump_313 : (((p0 ∨ p6) → (p2 ∨ True)) ∨ ((p6 → True) → False)) := by
                  apply Or.inl
                  intro assump_110
                  cases assump_110
                  case inl assump_111 =>
                    apply Or.inl
                    exact assump_103
                  case inr assump_112 =>
                    apply Or.inl
                    exact assump_103
                let assump_109 := assump_3 assump_313
                apply False.elim assump_109
              case inr assump_104 =>
                have assump_314 : (((p0 ∨ p6) → (p2 ∨ True)) ∨ ((p6 → True) → False)) := by
                  apply Or.inl
                  intro assump_125
                  cases assump_125
                  case inl assump_126 =>
                    apply Or.inl
                    exact assump_104
                  case inr assump_127 =>
                    apply Or.inl
                    exact assump_104
                let assump_124 := assump_3 assump_314
                apply False.elim assump_124
            case inr assump_102 =>
              cases assump_102
              case inl assump_135 =>
                apply False.elim assump_135
              case inr assump_136 =>
                have assump_315 : (((p0 ∨ p6) → (p2 ∨ True)) ∨ ((p6 → True) → False)) := by
                  apply Or.inl
                  intro assump_144
                  cases assump_144
                  case inl assump_145 =>
                    apply Or.inl
                    exact assump_136
                  case inr assump_146 =>
                    apply Or.inl
                    exact assump_136
                let assump_143 := assump_3 assump_315
                apply False.elim assump_143
      case inr assump_7 =>
        cases assump_7
        case intro assump_154 assump_155 =>
          cases assump_154
          case intro assump_156 assump_157 =>
            cases assump_155
            case inl assump_162 =>
              cases assump_5
              case inl assump_166 =>
                have assump_316 : (((p0 ∨ p6) → (p2 ∨ True)) ∨ ((p6 → True) → False)) := by
                  apply Or.inl
                  intro assump_173
                  cases assump_173
                  case inl assump_174 =>
                    apply Or.inr
                    apply True.intro
                  case inr assump_175 =>
                    apply Or.inr
                    apply True.intro
                let assump_172 := assump_3 assump_316
                apply False.elim assump_172
              case inr assump_167 =>
                cases assump_167
                case inl assump_183 =>
                  cases assump_183
                  case inl assump_185 =>
                    have assump_317 : (((p0 ∨ p6) → (p2 ∨ True)) ∨ ((p6 → True) → False)) := by
                      apply Or.inl
                      intro assump_192
                      cases assump_192
                      case inl assump_193 =>
                        apply Or.inl
                        exact assump_185
                      case inr assump_194 =>
                        apply Or.inl
                        exact assump_185
                    let assump_191 := assump_3 assump_317
                    apply False.elim assump_191
                  case inr assump_186 =>
                    have assump_318 : (((p0 ∨ p6) → (p2 ∨ True)) ∨ ((p6 → True) → False)) := by
                      apply Or.inl
                      intro assump_207
                      cases assump_207
                      case inl assump_208 =>
                        apply Or.inl
                        exact assump_186
                      case inr assump_209 =>
                        apply Or.inl
                        exact assump_186
                    let assump_206 := assump_3 assump_318
                    apply False.elim assump_206
                case inr assump_184 =>
                  cases assump_184
                  case inl assump_217 =>
                    apply False.elim assump_217
                  case inr assump_218 =>
                    have assump_319 : (((p0 ∨ p6) → (p2 ∨ True)) ∨ ((p6 → True) → False)) := by
                      apply Or.inl
                      intro assump_226
                      cases assump_226
                      case inl assump_227 =>
                        apply Or.inl
                        exact assump_218
                      case inr assump_228 =>
                        apply Or.inl
                        exact assump_218
                    let assump_225 := assump_3 assump_319
                    apply False.elim assump_225
            case inr assump_163 =>
              cases assump_5
              case inl assump_238 =>
                have assump_320 : (((p0 ∨ p6) → (p2 ∨ True)) ∨ ((p6 → True) → False)) := by
                  apply Or.inl
                  intro assump_245
                  cases assump_245
                  case inl assump_246 =>
                    apply Or.inr
                    apply True.intro
                  case inr assump_247 =>
                    apply Or.inr
                    apply True.intro
                let assump_244 := assump_3 assump_320
                apply False.elim assump_244
              case inr assump_239 =>
                cases assump_239
                case inl assump_255 =>
                  cases assump_255
                  case inl assump_257 =>
                    have assump_321 : (((p0 ∨ p6) → (p2 ∨ True)) ∨ ((p6 → True) → False)) := by
                      apply Or.inl
                      intro assump_264
                      cases assump_264
                      case inl assump_265 =>
                        apply Or.inl
                        exact assump_257
                      case inr assump_266 =>
                        apply Or.inl
                        exact assump_257
                    let assump_263 := assump_3 assump_321
                    apply False.elim assump_263
                  case inr assump_258 =>
                    have assump_322 : (((p0 ∨ p6) → (p2 ∨ True)) ∨ ((p6 → True) → False)) := by
                      apply Or.inl
                      intro assump_279
                      cases assump_279
                      case inl assump_280 =>
                        apply Or.inl
                        exact assump_258
                      case inr assump_281 =>
                        apply Or.inl
                        exact assump_258
                    let assump_278 := assump_3 assump_322
                    apply False.elim assump_278
                case inr assump_256 =>
                  cases assump_256
                  case inl assump_289 =>
                    apply False.elim assump_289
                  case inr assump_290 =>
                    have assump_323 : (((p0 ∨ p6) → (p2 ∨ True)) ∨ ((p6 → True) → False)) := by
                      apply Or.inl
                      intro assump_298
                      cases assump_298
                      case inl assump_299 =>
                        apply Or.inl
                        exact assump_290
                      case inr assump_300 =>
                        apply Or.inl
                        exact assump_290
                    let assump_297 := assump_3 assump_323
                    apply False.elim assump_297


variable (p4 p2 p7 p6 p5 p3 p1 : Prop)
theorem file97_26768 : (((((p6 ∧ p6) ∧ (p3 → False)) ∧ ((False → p3) → False)) → (((p4 → p6) ∨ (p3 → False)) → ((False ∧ p7) → False))) ∨ ((((p1 ∧ p1) → False) → ((p5 ∨ p2) → False)) ∨ (((p7 ∧ False) → False) → ((p6 ∧ True) ∨ (True → True))))) := by
  apply Or.inl
  intro assump_10
  intro assump_11
  intro assump_12
  cases assump_12
  case intro assump_13 assump_14 =>
    apply False.elim assump_13


variable (p5 p2 p7 p1 p4 p6 : Prop)
theorem file97_27209 : (((((False → p7) ∨ (p2 → p5)) → False) → False) ∨ ((((p1 → False) ∧ (p7 → p6)) ∨ ((False → True) ∧ (p4 ∨ p5))) → False)) := by
  apply Or.inl
  intro assump_1
  have assump_11 : ((False → p7) ∨ (p2 → p5)) := by
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p7 p6 p2 p1 p3 p4 p0 : Prop)
theorem file97_27614 : ((((((p1 ∧ False) ∧ (p7 → False)) ∧ ((p2 ∨ p0) ∨ (p2 → False))) ∧ (((p0 ∧ p7) → (p2 ∨ p3)) → ((p4 → p6) ∧ (p7 → False)))) ∧ ((((p7 → p7) → False) ∨ ((p7 → p2) → False)) → (((p0 → False) ∧ (True → True)) → ((p6 ∧ p1) → (False → False))))) → False) := by
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
            apply False.elim assump_11


variable (p3 p7 p0 p1 p6 p2 p5 : Prop)
theorem file97_28283 : (((((p3 → p5) ∨ (p7 → p1)) ∨ ((p2 ∧ p2) ∧ (p5 → False))) ∨ (((p1 ∧ p7) ∧ (p0 → False)) → False)) → ((((p6 → p6) → False) ∧ ((p5 ∧ p1) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_1
    case inl assump_9 =>
      cases assump_9
      case inl assump_11 =>
        cases assump_11
        case inl assump_13 =>
          have assump_69 : (p6 → p6) := by
            intro assump_20
            exact assump_20
          let assump_19 := assump_3 assump_69
          apply False.elim assump_19
        case inr assump_14 =>
          have assump_70 : (p6 → p6) := by
            intro assump_31
            exact assump_31
          let assump_30 := assump_3 assump_70
          apply False.elim assump_30
      case inr assump_12 =>
        cases assump_12
        case intro assump_37 assump_38 =>
          cases assump_37
          case intro assump_39 assump_40 =>
            have assump_71 : (p6 → p6) := by
              intro assump_52
              exact assump_52
            let assump_51 := assump_3 assump_71
            apply False.elim assump_51
    case inr assump_10 =>
      have assump_72 : (p6 → p6) := by
        intro assump_63
        exact assump_63
      let assump_62 := assump_3 assump_72
      apply False.elim assump_62


variable (p7 p0 p2 p6 : Prop)
theorem file97_29667 : ((((((p0 → True) → False) ∧ ((p7 → False) → False)) → False) ∧ ((((p2 ∧ p6) ∧ (p0 ∧ False)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_27 : (((p2 ∧ p6) ∧ (p0 ∧ False)) → False) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_11
          case intro assump_18 assump_19 =>
            apply False.elim assump_19
    let assump_8 := assump_3 assump_27
    apply False.elim assump_8


variable (p7 p3 p2 p4 p0 p1 : Prop)
theorem file97_30311 : ((((((p1 ∨ p7) ∧ (p0 → False)) ∨ ((p4 ∨ p3) ∨ (p4 → False))) ∨ (((p2 ∧ True) ∨ (p7 ∧ False)) → False)) → False) → False) := by
  intro assump_5
  have assump_20 : ((((p1 ∨ p7) ∧ (p0 → False)) ∨ ((p4 ∨ p3) ∨ (p4 → False))) ∨ (((p2 ∧ True) ∨ (p7 ∧ False)) → False)) := by
    apply Or.inl
    apply Or.inr
    apply Or.inr
    intro assump_9
    have assump_21 : ((((p1 ∨ p7) ∧ (p0 → False)) ∨ ((p4 ∨ p3) ∨ (p4 → False))) ∨ (((p2 ∧ True) ∨ (p7 ∧ False)) → False)) := by
      apply Or.inl
      apply Or.inr
      apply Or.inl
      apply Or.inl
      exact assump_9
    let assump_13 := assump_5 assump_21
    apply False.elim assump_13
  let assump_8 := assump_5 assump_20
  apply False.elim assump_8


variable (p3 p2 p5 p7 p0 p1 p6 p4 : Prop)
theorem file97_31078 : (((((p7 ∨ p6) → False) → False) ∧ (((p6 → p3) ∨ (p4 → False)) ∧ ((True → False) ∧ (p5 ∧ True)))) → ((((True → False) → False) ∧ ((p1 ∨ p0) ∨ (p5 ∨ p6))) ∨ (((p2 ∨ p5) ∧ (p4 ∧ False)) ∨ ((p0 ∧ p1) → (p2 ∨ False))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case intro assump_12 assump_13 =>
          cases assump_13
          case intro assump_16 assump_17 =>
            apply Or.inl
            apply And.intro
            intro assump_22
            have assump_48 : True := by
              apply True.intro
            let assump_25 := assump_22 assump_48
            apply False.elim assump_25
            apply Or.inr
            apply Or.inl
            exact assump_16
      case inr assump_9 =>
        cases assump_7
        case intro assump_31 assump_32 =>
          cases assump_32
          case intro assump_35 assump_36 =>
            apply Or.inl
            apply And.intro
            intro assump_41
            have assump_49 : True := by
              apply True.intro
            let assump_44 := assump_41 assump_49
            apply False.elim assump_44
            apply Or.inr
            apply Or.inl
            exact assump_35


variable (p0 p1 p3 p6 p4 p5 p7 : Prop)
theorem file97_32466 : (((((p6 ∧ p7) ∧ (p5 ∨ p1)) ∧ ((p0 → p3) → False)) ∧ (((p1 ∨ p3) ∨ (p5 → p7)) → ((False ∧ p1) ∧ (p6 ∨ True)))) → ((((p0 ∨ p3) → (p4 ∨ p3)) ∨ ((p1 → True) ∨ (p5 → False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_9
        case intro assump_11 assump_12 =>
          cases assump_11
          case intro assump_13 assump_14 =>
            cases assump_12
            case inl assump_19 =>
              have assump_136 : ((p1 ∨ p3) ∨ (p5 → p7)) := by
                apply Or.inr
                intro assump_28
                exact assump_14
              let assump_27 := assump_8 assump_136
              let assump_31 := And.left assump_27
              let assump_32 := And.left assump_31
              apply False.elim assump_32
            case inr assump_20 =>
              have assump_137 : ((p1 ∨ p3) ∨ (p5 → p7)) := by
                apply Or.inl
                apply Or.inl
                exact assump_20
              let assump_42 := assump_8 assump_137
              let assump_43 := And.left assump_42
              let assump_44 := And.left assump_43
              apply False.elim assump_44
  case inr assump_4 =>
    cases assump_4
    case inl assump_48 =>
      cases assump_1
      case intro assump_52 assump_53 =>
        cases assump_52
        case intro assump_54 assump_55 =>
          cases assump_54
          case intro assump_56 assump_57 =>
            cases assump_56
            case intro assump_58 assump_59 =>
              cases assump_57
              case inl assump_64 =>
                have assump_138 : ((p1 ∨ p3) ∨ (p5 → p7)) := by
                  apply Or.inr
                  intro assump_73
                  exact assump_59
                let assump_72 := assump_53 assump_138
                let assump_76 := And.left assump_72
                let assump_77 := And.left assump_76
                apply False.elim assump_77
              case inr assump_65 =>
                have assump_139 : ((p1 ∨ p3) ∨ (p5 → p7)) := by
                  apply Or.inl
                  apply Or.inl
                  exact assump_65
                let assump_87 := assump_53 assump_139
                let assump_88 := And.left assump_87
                let assump_89 := And.left assump_88
                apply False.elim assump_89
    case inr assump_49 =>
      cases assump_1
      case intro assump_95 assump_96 =>
        cases assump_95
        case intro assump_97 assump_98 =>
          cases assump_97
          case intro assump_99 assump_100 =>
            cases assump_99
            case intro assump_101 assump_102 =>
              cases assump_100
              case inl assump_107 =>
                have assump_140 : ((p1 ∨ p3) ∨ (p5 → p7)) := by
                  apply Or.inr
                  intro assump_116
                  exact assump_102
                let assump_115 := assump_96 assump_140
                let assump_119 := And.left assump_115
                let assump_120 := And.left assump_119
                apply False.elim assump_120
              case inr assump_108 =>
                have assump_141 : ((p1 ∨ p3) ∨ (p5 → p7)) := by
                  apply Or.inl
                  apply Or.inl
                  exact assump_108
                let assump_130 := assump_96 assump_141
                let assump_131 := And.left assump_130
                let assump_132 := And.left assump_131
                apply False.elim assump_132


variable (p2 p7 p6 p1 p4 p3 p5 p0 : Prop)
theorem file97_36140 : (((((p0 → True) → False) → False) ∧ (((p6 ∨ p2) ∧ (p4 → p5)) → ((p4 ∧ p1) → (p6 → p4)))) ∨ ((((False → p3) ∨ (p7 → False)) → ((p7 ∧ p1) ∧ (True ∨ p4))) → False)) := by
  apply Or.inl
  apply And.intro
  intro assump_16
  have assump_47 : (p0 → True) := by
    intro assump_20
    apply True.intro
  let assump_19 := assump_16 assump_47
  apply False.elim assump_19
  intro assump_24
  intro assump_25
  intro assump_26
  cases assump_25
  case intro assump_29 assump_30 =>
    cases assump_24
    case intro assump_35 assump_36 =>
      cases assump_35
      case inl assump_37 =>
        exact assump_29
      case inr assump_38 =>
        exact assump_29


variable (p1 p4 p7 p6 p2 p0 p5 p3 : Prop)
theorem file97_36863 : ((((((p7 → False) ∨ (True ∧ p5)) ∧ ((False ∧ p1) → (p6 → p3))) → (((p5 → p0) ∧ (p2 → p6)) ∨ ((False → False) → False))) ∧ ((((False ∧ p2) → False) ∨ ((p4 ∨ p2) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_17 : (((False ∧ p2) → False) ∨ ((p4 ∨ p2) → False)) := by
      apply Or.inl
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply False.elim assump_10
    let assump_8 := assump_3 assump_17
    apply False.elim assump_8


variable (p1 p4 p3 p2 p7 p6 p0 : Prop)
theorem file97_37468 : ((((((False → False) → (p7 → p6)) → False) ∧ (((p0 ∧ False) ∧ (p0 ∧ p3)) ∧ ((False → True) ∧ (True ∧ p4)))) ∧ ((((p1 ∧ p7) → False) ∧ ((p4 → p2) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            apply False.elim assump_13


variable (p3 p2 p7 p4 p0 : Prop)
theorem file97_38061 : ((((((True → False) ∧ (p7 → False)) → ((p3 ∨ True) → False)) ∨ (((p4 → p0) → False) ∨ ((p7 ∧ True) ∨ (p2 ∧ p0)))) → False) → False) := by
  intro assump_1
  have assump_38 : ((((True → False) ∧ (p7 → False)) → ((p3 ∨ True) → False)) ∨ (((p4 → p0) → False) ∨ ((p7 ∧ True) ∨ (p2 ∧ p0)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_5
      case intro assump_11 assump_12 =>
        have assump_39 : True := by
          apply True.intro
        let assump_18 := assump_11 assump_39
        apply False.elim assump_18
    case inr assump_8 =>
      cases assump_5
      case intro assump_24 assump_25 =>
        have assump_40 : True := by
          apply True.intro
        let assump_31 := assump_24 assump_40
        apply False.elim assump_31
  let assump_4 := assump_1 assump_38
  apply False.elim assump_4


variable (p2 p4 p7 p3 p0 p1 p5 : Prop)
theorem file97_39013 : (((((False ∧ p2) → (p1 → False)) → ((False → p0) ∨ (p7 → p1))) → False) → ((((p0 → False) → (p4 → False)) → False) → (((p4 ∨ p5) ∧ (p1 ∧ p3)) → ((p0 ∨ p2) → (p4 → False))))) := by
  intro assump_5
  intro assump_6
  intro assump_7
  intro assump_8
  intro assump_9
  cases assump_8
  case inl assump_12 =>
    cases assump_7
    case intro assump_16 assump_17 =>
      cases assump_16
      case inl assump_18 =>
        cases assump_17
        case intro assump_22 assump_23 =>
          have assump_114 : (((False ∧ p2) → (p1 → False)) → ((False → p0) ∨ (p7 → p1))) := by
            intro assump_33
            apply Or.inl
            intro assump_36
            apply False.elim assump_36
          let assump_32 := assump_5 assump_114
          apply False.elim assump_32
      case inr assump_19 =>
        cases assump_17
        case intro assump_44 assump_45 =>
          have assump_115 : (((False ∧ p2) → (p1 → False)) → ((False → p0) ∨ (p7 → p1))) := by
            intro assump_55
            apply Or.inl
            intro assump_58
            apply False.elim assump_58
          let assump_54 := assump_5 assump_115
          apply False.elim assump_54
  case inr assump_13 =>
    cases assump_7
    case intro assump_66 assump_67 =>
      cases assump_66
      case inl assump_68 =>
        cases assump_67
        case intro assump_72 assump_73 =>
          have assump_116 : (((False ∧ p2) → (p1 → False)) → ((False → p0) ∨ (p7 → p1))) := by
            intro assump_83
            apply Or.inl
            intro assump_86
            apply False.elim assump_86
          let assump_82 := assump_5 assump_116
          apply False.elim assump_82
      case inr assump_69 =>
        cases assump_67
        case intro assump_94 assump_95 =>
          have assump_117 : (((False ∧ p2) → (p1 → False)) → ((False → p0) ∨ (p7 → p1))) := by
            intro assump_105
            apply Or.inl
            intro assump_108
            apply False.elim assump_108
          let assump_104 := assump_5 assump_117
          apply False.elim assump_104


variable (p6 p4 p3 p0 p2 : Prop)
theorem file97_41135 : (((((True ∧ p2) → False) → ((p2 → p4) → False)) → False) → ((((p0 → False) → (p0 ∨ p3)) ∧ ((p3 ∧ p2) ∧ (p6 → p2))) → False)) := by
  intro assump_14
  intro assump_15
  cases assump_15
  case intro assump_16 assump_17 =>
    cases assump_17
    case intro assump_20 assump_21 =>
      cases assump_20
      case intro assump_22 assump_23 =>
        have assump_46 : (((True ∧ p2) → False) → ((p2 → p4) → False)) := by
          intro assump_33
          intro assump_34
          have assump_47 : (True ∧ p2) := by
            apply And.intro
            apply True.intro
            exact assump_23
          let assump_39 := assump_33 assump_47
          apply False.elim assump_39
        let assump_32 := assump_14 assump_46
        apply False.elim assump_32


variable (p2 p5 p6 p0 p1 p3 p7 p4 : Prop)
theorem file97_41965 : ((((((p7 ∧ False) ∨ (p5 → False)) ∧ ((p1 ∧ p2) → (p3 ∧ True))) → (((p6 ∨ p5) → (p5 → p6)) ∨ ((p0 → p5) ∨ (p5 ∨ p4)))) → False) → False) := by
  intro assump_1
  have assump_40 : ((((p7 ∧ False) ∨ (p5 → False)) ∧ ((p1 ∧ p2) → (p3 ∧ True))) → (((p6 ∨ p5) → (p5 → p6)) ∨ ((p0 → p5) ∨ (p5 ∨ p4)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply False.elim assump_11
      case inr assump_9 =>
        apply Or.inl
        intro assump_20
        intro assump_21
        cases assump_20
        case inl assump_24 =>
          exact assump_24
        case inr assump_25 =>
          have assump_41 : p5 := by
            exact assump_25
          let assump_33 := assump_9 assump_41
          apply False.elim assump_33
  let assump_4 := assump_1 assump_40
  apply False.elim assump_4


variable (p0 p4 p6 p2 : Prop)
theorem file97_42961 : (((((p0 → True) ∨ (p0 → False)) ∨ ((p2 ∧ p6) ∧ (p4 → False))) → False) → False) := by
  intro assump_1
  have assump_9 : (((p0 → True) ∨ (p0 → False)) ∨ ((p2 ∧ p6) ∧ (p4 → False))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_9
  apply False.elim assump_4


variable (p0 p2 : Prop)
theorem file97_43334 : ((((((p0 ∨ True) → (p2 → False)) ∧ ((True → False) ∧ (False ∧ False))) → False) → False) → False) := by
  intro assump_1
  have assump_21 : ((((p0 ∨ True) → (p2 → False)) ∧ ((True → False) ∧ (False ∧ False))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          apply False.elim assump_14
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p7 p2 p6 p4 p1 : Prop)
theorem file97_43918 : ((((((False → p2) ∨ (p1 ∧ True)) → False) → (((p4 ∧ p6) ∧ (p7 → False)) → ((p7 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_32 : ((((False → p2) ∨ (p1 ∧ True)) → False) → (((p4 ∧ p6) ∧ (p7 → False)) → ((p7 → False) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        have assump_33 : ((False → p2) ∨ (p1 ∧ True)) := by
          apply Or.inl
          intro assump_23
          apply False.elim assump_23
        let assump_22 := assump_5 assump_33
        apply False.elim assump_22
  let assump_4 := assump_1 assump_32
  apply False.elim assump_4


variable (p0 p7 p3 p1 p6 p5 : Prop)
theorem file97_44706 : (((((p3 ∧ p0) ∧ (p0 → False)) → False) ∨ (((p3 → False) → False) ∧ ((p0 ∨ p1) ∨ (p5 → p1)))) ∨ ((((False → False) → (p3 ∨ True)) ∨ ((p3 → False) → (p7 → True))) → (((False → p3) → (p5 → False)) → ((p7 ∧ p7) ∨ (p6 → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_16 : p0 := by
        exact assump_5
      let assump_12 := assump_3 assump_16
      apply False.elim assump_12


variable (p3 p1 p4 p6 p2 p5 : Prop)
theorem file97_45281 : (((((p5 ∨ p3) ∧ (p5 ∧ p4)) → ((p6 ∨ p5) → (p2 → False))) ∧ (((p2 ∧ p4) ∧ (p6 → p6)) ∧ ((p1 → p1) → (p4 → False)))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_7
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_12
        case intro assump_14 assump_15 =>
          have assump_32 : (p1 → p1) := by
            intro assump_25
            exact assump_25
          let assump_24 := assump_11 assump_32
          have assump_33 : p4 := by
            exact assump_15
          let assump_28 := assump_24 assump_33
          apply False.elim assump_28


variable (p5 p4 p1 p2 p6 p3 p0 : Prop)
theorem file97_46021 : (((((p3 → True) ∨ (p5 → False)) → False) → False) ∨ ((((p0 → False) → False) → False) ∨ (((p4 → False) ∨ (p6 ∧ p1)) → ((p4 → p2) → (False → False))))) := by
  apply Or.inl
  intro assump_1
  have assump_9 : ((p3 → True) ∨ (p5 → False)) := by
    apply Or.inl
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_9
  apply False.elim assump_4


variable (p1 p0 p7 p6 p4 p5 : Prop)
theorem file97_46444 : (((((p5 ∧ p6) ∨ (p5 → p7)) → False) → (((p6 ∧ p5) ∨ (p4 ∧ p7)) → ((p7 ∨ p1) → (False → False)))) ∨ ((((p7 ∨ p1) ∧ (False → p6)) → False) → (((p5 ∧ False) ∨ (p0 → True)) → False))) := by
  apply Or.inl
  intro assump_15
  intro assump_16
  intro assump_17
  intro assump_18
  apply False.elim assump_18


variable (p5 p0 p2 p4 p3 p6 p1 p7 : Prop)
theorem file97_46812 : (((((p3 → False) ∨ (p4 → False)) ∧ ((p5 ∨ p2) ∧ (p2 → p2))) ∧ (((p6 → False) ∨ (p0 ∧ p6)) ∧ ((p3 → False) ∨ (p2 ∨ p7)))) → ((((p1 ∨ True) ∨ (p5 → p5)) → False) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_8
        case intro assump_13 assump_14 =>
          cases assump_13
          case inl assump_15 =>
            cases assump_6
            case intro assump_21 assump_22 =>
              cases assump_21
              case inl assump_23 =>
                cases assump_22
                case inl assump_27 =>
                  have assump_411 : ((p1 ∨ True) ∨ (p5 → p5)) := by
                    apply Or.inl
                    apply Or.inr
                    apply True.intro
                  let assump_36 := assump_2 assump_411
                  apply False.elim assump_36
                case inr assump_28 =>
                  cases assump_28
                  case inl assump_40 =>
                    have assump_412 : ((p1 ∨ True) ∨ (p5 → p5)) := by
                      apply Or.inl
                      apply Or.inr
                      apply True.intro
                    let assump_50 := assump_2 assump_412
                    apply False.elim assump_50
                  case inr assump_41 =>
                    have assump_413 : ((p1 ∨ True) ∨ (p5 → p5)) := by
                      apply Or.inl
                      apply Or.inr
                      apply True.intro
                    let assump_61 := assump_2 assump_413
                    apply False.elim assump_61
              case inr assump_24 =>
                cases assump_24
                case intro assump_65 assump_66 =>
                  cases assump_22
                  case inl assump_71 =>
                    have assump_414 : ((p1 ∨ True) ∨ (p5 → p5)) := by
                      apply Or.inl
                      apply Or.inr
                      apply True.intro
                    let assump_81 := assump_2 assump_414
                    apply False.elim assump_81
                  case inr assump_72 =>
                    cases assump_72
                    case inl assump_85 =>
                      have assump_415 : ((p1 ∨ True) ∨ (p5 → p5)) := by
                        apply Or.inl
                        apply Or.inr
                        apply True.intro
                      let assump_96 := assump_2 assump_415
                      apply False.elim assump_96
                    case inr assump_86 =>
                      have assump_416 : ((p1 ∨ True) ∨ (p5 → p5)) := by
                        apply Or.inl
                        apply Or.inr
                        apply True.intro
                      let assump_108 := assump_2 assump_416
                      apply False.elim assump_108
          case inr assump_16 =>
            cases assump_6
            case intro assump_116 assump_117 =>
              cases assump_116
              case inl assump_118 =>
                cases assump_117
                case inl assump_122 =>
                  have assump_417 : ((p1 ∨ True) ∨ (p5 → p5)) := by
                    apply Or.inl
                    apply Or.inr
                    apply True.intro
                  let assump_132 := assump_2 assump_417
                  apply False.elim assump_132
                case inr assump_123 =>
                  cases assump_123
                  case inl assump_136 =>
                    have assump_418 : ((p1 ∨ True) ∨ (p5 → p5)) := by
                      apply Or.inl
                      apply Or.inr
                      apply True.intro
                    let assump_146 := assump_2 assump_418
                    apply False.elim assump_146
                  case inr assump_137 =>
                    have assump_419 : ((p1 ∨ True) ∨ (p5 → p5)) := by
                      apply Or.inl
                      apply Or.inr
                      apply True.intro
                    let assump_158 := assump_2 assump_419
                    apply False.elim assump_158
              case inr assump_119 =>
                cases assump_119
                case intro assump_162 assump_163 =>
                  cases assump_117
                  case inl assump_168 =>
                    have assump_420 : ((p1 ∨ True) ∨ (p5 → p5)) := by
                      apply Or.inl
                      apply Or.inr
                      apply True.intro
                    let assump_179 := assump_2 assump_420
                    apply False.elim assump_179
                  case inr assump_169 =>
                    cases assump_169
                    case inl assump_183 =>
                      have assump_421 : ((p1 ∨ True) ∨ (p5 → p5)) := by
                        apply Or.inl
                        apply Or.inr
                        apply True.intro
                      let assump_194 := assump_2 assump_421
                      apply False.elim assump_194
                    case inr assump_184 =>
                      have assump_422 : ((p1 ∨ True) ∨ (p5 → p5)) := by
                        apply Or.inl
                        apply Or.inr
                        apply True.intro
                      let assump_207 := assump_2 assump_422
                      apply False.elim assump_207
      case inr assump_10 =>
        cases assump_8
        case intro assump_213 assump_214 =>
          cases assump_213
          case inl assump_215 =>
            cases assump_6
            case intro assump_221 assump_222 =>
              cases assump_221
              case inl assump_223 =>
                cases assump_222
                case inl assump_227 =>
                  have assump_423 : ((p1 ∨ True) ∨ (p5 → p5)) := by
                    apply Or.inl
                    apply Or.inr
                    apply True.intro
                  let assump_236 := assump_2 assump_423
                  apply False.elim assump_236
                case inr assump_228 =>
                  cases assump_228
                  case inl assump_240 =>
                    have assump_424 : ((p1 ∨ True) ∨ (p5 → p5)) := by
                      apply Or.inl
                      apply Or.inr
                      apply True.intro
                    let assump_250 := assump_2 assump_424
                    apply False.elim assump_250
                  case inr assump_241 =>
                    have assump_425 : ((p1 ∨ True) ∨ (p5 → p5)) := by
                      apply Or.inl
                      apply Or.inr
                      apply True.intro
                    let assump_261 := assump_2 assump_425
                    apply False.elim assump_261
              case inr assump_224 =>
                cases assump_224
                case intro assump_265 assump_266 =>
                  cases assump_222
                  case inl assump_271 =>
                    have assump_426 : ((p1 ∨ True) ∨ (p5 → p5)) := by
                      apply Or.inl
                      apply Or.inr
                      apply True.intro
                    let assump_281 := assump_2 assump_426
                    apply False.elim assump_281
                  case inr assump_272 =>
                    cases assump_272
                    case inl assump_285 =>
                      have assump_427 : ((p1 ∨ True) ∨ (p5 → p5)) := by
                        apply Or.inl
                        apply Or.inr
                        apply True.intro
                      let assump_296 := assump_2 assump_427
                      apply False.elim assump_296
                    case inr assump_286 =>
                      have assump_428 : ((p1 ∨ True) ∨ (p5 → p5)) := by
                        apply Or.inl
                        apply Or.inr
                        apply True.intro
                      let assump_308 := assump_2 assump_428
                      apply False.elim assump_308
          case inr assump_216 =>
            cases assump_6
            case intro assump_316 assump_317 =>
              cases assump_316
              case inl assump_318 =>
                cases assump_317
                case inl assump_322 =>
                  have assump_429 : ((p1 ∨ True) ∨ (p5 → p5)) := by
                    apply Or.inl
                    apply Or.inr
                    apply True.intro
                  let assump_332 := assump_2 assump_429
                  apply False.elim assump_332
                case inr assump_323 =>
                  cases assump_323
                  case inl assump_336 =>
                    have assump_430 : ((p1 ∨ True) ∨ (p5 → p5)) := by
                      apply Or.inl
                      apply Or.inr
                      apply True.intro
                    let assump_346 := assump_2 assump_430
                    apply False.elim assump_346
                  case inr assump_337 =>
                    have assump_431 : ((p1 ∨ True) ∨ (p5 → p5)) := by
                      apply Or.inl
                      apply Or.inr
                      apply True.intro
                    let assump_358 := assump_2 assump_431
                    apply False.elim assump_358
              case inr assump_319 =>
                cases assump_319
                case intro assump_362 assump_363 =>
                  cases assump_317
                  case inl assump_368 =>
                    have assump_432 : ((p1 ∨ True) ∨ (p5 → p5)) := by
                      apply Or.inl
                      apply Or.inr
                      apply True.intro
                    let assump_379 := assump_2 assump_432
                    apply False.elim assump_379
                  case inr assump_369 =>
                    cases assump_369
                    case inl assump_383 =>
                      have assump_433 : ((p1 ∨ True) ∨ (p5 → p5)) := by
                        apply Or.inl
                        apply Or.inr
                        apply True.intro
                      let assump_394 := assump_2 assump_433
                      apply False.elim assump_394
                    case inr assump_384 =>
                      have assump_434 : ((p1 ∨ True) ∨ (p5 → p5)) := by
                        apply Or.inl
                        apply Or.inr
                        apply True.intro
                      let assump_407 := assump_2 assump_434
                      apply False.elim assump_407


variable (p5 p4 p3 p7 p6 : Prop)
theorem file97_57366 : ((((((p5 ∨ p6) ∧ (True → p7)) ∧ ((p7 ∧ p5) ∧ (p3 ∧ p3))) ∧ (((True ∧ False) → (p4 → p6)) → False)) ∧ ((((p3 → p6) ∨ (p6 ∧ p7)) → False) ∧ (((p7 → p7) → False) ∧ ((p7 → False) ∧ (True ∧ p6))))) → False) := by
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
          case inl assump_10 =>
            cases assump_7
            case intro assump_16 assump_17 =>
              cases assump_16
              case intro assump_18 assump_19 =>
                cases assump_17
                case intro assump_24 assump_25 =>
                  cases assump_3
                  case intro assump_32 assump_33 =>
                    cases assump_33
                    case intro assump_36 assump_37 =>
                      cases assump_37
                      case intro assump_40 assump_41 =>
                        cases assump_41
                        case intro assump_44 assump_45 =>
                          have assump_98 : p7 := by
                            exact assump_18
                          let assump_51 := assump_40 assump_98
                          apply False.elim assump_51
          case inr assump_11 =>
            cases assump_7
            case intro assump_59 assump_60 =>
              cases assump_59
              case intro assump_61 assump_62 =>
                cases assump_60
                case intro assump_67 assump_68 =>
                  cases assump_3
                  case intro assump_75 assump_76 =>
                    cases assump_76
                    case intro assump_79 assump_80 =>
                      cases assump_80
                      case intro assump_83 assump_84 =>
                        cases assump_84
                        case intro assump_87 assump_88 =>
                          have assump_99 : p7 := by
                            exact assump_61
                          let assump_94 := assump_83 assump_99
                          apply False.elim assump_94


variable (p3 p7 p1 p2 p6 p0 : Prop)
theorem file97_59592 : (((((p1 → False) ∧ (p0 → False)) → False) → False) → ((((True ∨ False) → (p2 ∨ p2)) → False) → (((p6 ∧ p0) → (p6 → False)) ∨ ((p1 ∨ p3) ∨ (p7 → False))))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  intro assump_8
  cases assump_7
  case intro assump_11 assump_12 =>
    have assump_35 : (((p1 → False) ∧ (p0 → False)) → False) := by
      intro assump_21
      cases assump_21
      case intro assump_22 assump_23 =>
        have assump_36 : p0 := by
          exact assump_12
        let assump_28 := assump_23 assump_36
        apply False.elim assump_28
    let assump_20 := assump_1 assump_35
    apply False.elim assump_20


variable (p4 p5 p0 p3 p7 p2 p1 p6 : Prop)
theorem file97_60317 : ((((((True ∧ p5) → (p4 → False)) → False) ∨ (((p6 → False) → (p3 → False)) → ((p7 → p3) → (False ∧ p4)))) ∧ ((((p0 ∨ p4) ∧ (False ∧ p1)) ∧ ((p4 → False) → (False ∨ p4))) ∧ (((p4 ∧ p5) → (p2 ∨ p1)) → ((True ∧ p7) → False)))) → False) := by
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
            case inl assump_14 =>
              cases assump_13
              case intro assump_18 assump_19 =>
                apply False.elim assump_18
            case inr assump_15 =>
              cases assump_13
              case intro assump_24 assump_25 =>
                apply False.elim assump_24
    case inr assump_5 =>
      cases assump_3
      case intro assump_30 assump_31 =>
        cases assump_30
        case intro assump_32 assump_33 =>
          cases assump_32
          case intro assump_34 assump_35 =>
            cases assump_34
            case inl assump_36 =>
              cases assump_35
              case intro assump_40 assump_41 =>
                apply False.elim assump_40
            case inr assump_37 =>
              cases assump_35
              case intro assump_46 assump_47 =>
                apply False.elim assump_46


variable (p7 p6 p2 p5 p3 p0 : Prop)
theorem file97_61820 : (((((p5 → p0) → (p6 ∧ p0)) ∧ ((p0 → False) ∨ (p2 → False))) → False) → ((((True ∨ p7) → (p3 ∨ p6)) ∧ ((p0 ∨ p6) ∧ (p3 ∧ False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_8
        case intro assump_13 assump_14 =>
          apply False.elim assump_14
      case inr assump_10 =>
        cases assump_8
        case intro assump_21 assump_22 =>
          apply False.elim assump_22


variable (p7 p4 p0 p3 p1 p5 : Prop)
theorem file97_62445 : ((((((True → False) → (False ∨ p1)) ∧ ((p4 → True) → (p3 → False))) → (((p7 → p5) → (p1 ∨ p3)) ∨ ((p0 → p4) → False))) ∧ ((((p5 → p4) → False) → False) ∧ (((p3 → False) → False) ∧ ((p3 → p3) → (p3 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        have assump_37 : (p3 → False) := by
          intro assump_22
          have assump_38 : (p3 → p3) := by
            intro assump_27
            exact assump_27
          let assump_26 := assump_11 assump_38
          have assump_39 : p3 := by
            exact assump_22
          let assump_30 := assump_26 assump_39
          apply False.elim assump_30
        let assump_21 := assump_10 assump_37
        apply False.elim assump_21


variable (p7 p3 p1 : Prop)
theorem file97_63349 : ((((((p1 → False) ∧ (p7 ∧ p1)) → ((False ∨ p7) ∨ (p3 ∨ p7))) → False) ∧ ((((False → False) → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_22 : (((False → False) → False) → False) := by
      intro assump_9
      have assump_23 : (False → False) := by
        intro assump_13
        apply False.elim assump_13
      let assump_12 := assump_9 assump_23
      apply False.elim assump_12
    let assump_8 := assump_3 assump_22
    apply False.elim assump_8


variable (p5 p3 p7 p1 p4 : Prop)
theorem file97_63940 : (((((p7 → False) ∧ (False ∧ p5)) ∧ ((p3 ∨ p5) ∨ (True → False))) ∧ (((p4 ∧ p4) → False) → ((p4 ∨ p5) ∨ (p3 → p1)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          apply False.elim assump_10


variable (p4 p5 p7 p2 p1 p6 : Prop)
theorem file97_64415 : ((((((p6 ∨ p5) ∧ (p7 ∨ False)) ∨ ((p2 → p1) ∧ (p1 → False))) → (((p2 ∨ False) ∨ (False → False)) ∨ ((p4 ∨ p4) → (p7 → True)))) → False) → False) := by
  intro assump_1
  have assump_46 : ((((p6 ∨ p5) ∧ (p7 ∨ False)) ∨ ((p2 → p1) ∧ (p1 → False))) → (((p2 ∨ False) ∨ (False → False)) ∨ ((p4 ∨ p4) → (p7 → True)))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_9
          case inl assump_14 =>
            apply Or.inl
            apply Or.inr
            intro assump_18
            apply False.elim assump_18
          case inr assump_15 =>
            apply False.elim assump_15
        case inr assump_11 =>
          cases assump_9
          case inl assump_25 =>
            apply Or.inl
            apply Or.inr
            intro assump_29
            apply False.elim assump_29
          case inr assump_26 =>
            apply False.elim assump_26
    case inr assump_7 =>
      cases assump_7
      case intro assump_34 assump_35 =>
        apply Or.inl
        apply Or.inr
        intro assump_40
        apply False.elim assump_40
  let assump_4 := assump_1 assump_46
  apply False.elim assump_4


variable (p4 p1 p3 p2 p6 p7 : Prop)
theorem file97_65740 : ((((((p1 → p1) ∨ (p6 ∧ p4)) ∧ ((True → False) → False)) ∧ (((True → True) → (p7 ∧ True)) ∨ ((p2 → False) ∨ (p2 ∧ True)))) ∧ ((((p6 → False) ∧ (p3 → False)) → ((p6 ∨ p3) → (p7 → p7))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_5
          case inl assump_14 =>
            have assump_224 : (((p6 → False) ∧ (p3 → False)) → ((p6 ∨ p3) → (p7 → p7))) := by
              intro assump_21
              intro assump_22
              intro assump_23
              cases assump_22
              case inl assump_26 =>
                cases assump_21
                case intro assump_30 assump_31 =>
                  exact assump_23
              case inr assump_27 =>
                cases assump_21
                case intro assump_38 assump_39 =>
                  exact assump_23
            let assump_20 := assump_3 assump_224
            apply False.elim assump_20
          case inr assump_15 =>
            cases assump_15
            case inl assump_47 =>
              have assump_225 : (((p6 → False) ∧ (p3 → False)) → ((p6 ∨ p3) → (p7 → p7))) := by
                intro assump_54
                intro assump_55
                intro assump_56
                cases assump_55
                case inl assump_59 =>
                  cases assump_54
                  case intro assump_63 assump_64 =>
                    exact assump_56
                case inr assump_60 =>
                  cases assump_54
                  case intro assump_71 assump_72 =>
                    exact assump_56
              let assump_53 := assump_3 assump_225
              apply False.elim assump_53
            case inr assump_48 =>
              cases assump_48
              case intro assump_80 assump_81 =>
                have assump_226 : (((p6 → False) ∧ (p3 → False)) → ((p6 ∨ p3) → (p7 → p7))) := by
                  intro assump_89
                  intro assump_90
                  intro assump_91
                  cases assump_90
                  case inl assump_94 =>
                    cases assump_89
                    case intro assump_98 assump_99 =>
                      exact assump_91
                  case inr assump_95 =>
                    cases assump_89
                    case intro assump_106 assump_107 =>
                      exact assump_91
                let assump_88 := assump_3 assump_226
                apply False.elim assump_88
        case inr assump_9 =>
          cases assump_9
          case intro assump_115 assump_116 =>
            cases assump_5
            case inl assump_123 =>
              have assump_227 : (((p6 → False) ∧ (p3 → False)) → ((p6 ∨ p3) → (p7 → p7))) := by
                intro assump_130
                intro assump_131
                intro assump_132
                cases assump_131
                case inl assump_135 =>
                  cases assump_130
                  case intro assump_139 assump_140 =>
                    exact assump_132
                case inr assump_136 =>
                  cases assump_130
                  case intro assump_147 assump_148 =>
                    exact assump_132
              let assump_129 := assump_3 assump_227
              apply False.elim assump_129
            case inr assump_124 =>
              cases assump_124
              case inl assump_156 =>
                have assump_228 : (((p6 → False) ∧ (p3 → False)) → ((p6 ∨ p3) → (p7 → p7))) := by
                  intro assump_163
                  intro assump_164
                  intro assump_165
                  cases assump_164
                  case inl assump_168 =>
                    cases assump_163
                    case intro assump_172 assump_173 =>
                      exact assump_165
                  case inr assump_169 =>
                    cases assump_163
                    case intro assump_180 assump_181 =>
                      exact assump_165
                let assump_162 := assump_3 assump_228
                apply False.elim assump_162
              case inr assump_157 =>
                cases assump_157
                case intro assump_189 assump_190 =>
                  have assump_229 : (((p6 → False) ∧ (p3 → False)) → ((p6 ∨ p3) → (p7 → p7))) := by
                    intro assump_198
                    intro assump_199
                    intro assump_200
                    cases assump_199
                    case inl assump_203 =>
                      cases assump_198
                      case intro assump_207 assump_208 =>
                        exact assump_200
                    case inr assump_204 =>
                      cases assump_198
                      case intro assump_215 assump_216 =>
                        exact assump_200
                  let assump_197 := assump_3 assump_229
                  apply False.elim assump_197


variable (p0 p7 p2 p4 p5 p3 p1 : Prop)
theorem file97_70851 : ((((((p4 ∨ True) → False) → ((p7 → p2) ∨ (p5 ∨ p7))) → False) ∧ ((((False ∧ True) ∧ (p4 ∧ p0)) ∧ ((p0 → p7) → (p1 → p3))) → (((True → False) → False) ∨ ((p1 ∨ p0) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_24 : (((p4 ∨ True) → False) → ((p7 → p2) ∨ (p5 ∨ p7))) := by
      intro assump_10
      apply Or.inl
      intro assump_13
      have assump_25 : (p4 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_17 := assump_10 assump_25
      apply False.elim assump_17
    let assump_9 := assump_2 assump_24
    apply False.elim assump_9


variable (p5 p6 p4 p0 p1 : Prop)
theorem file97_71538 : (((((p0 ∨ p5) → (p4 ∨ True)) → False) → (((p6 → False) → False) → ((False ∨ False) ∨ (True ∨ p4)))) ∨ ((((p1 → False) → False) → ((p4 → False) → (p1 → False))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply Or.inr
  apply Or.inl
  apply True.intro


variable (p6 p1 p7 p4 p0 p3 p5 p2 : Prop)
theorem file97_71878 : (((((p1 → False) → (True ∧ p6)) ∨ ((p0 → False) ∧ (p1 → False))) ∧ (((p4 → False) ∨ (p2 ∧ p6)) ∨ ((p2 → False) → False))) → ((((p3 → False) ∨ (True → False)) → ((p2 → False) ∧ (p3 ∨ p3))) → (((True ∧ True) → (False → p7)) → ((p5 → p0) → (False → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  intro assump_5
  apply False.elim assump_5


variable (p6 p7 p1 p4 p5 p0 p3 p2 : Prop)
theorem file97_72320 : (((((True ∨ p0) → False) → ((p5 → False) → False)) ∨ (((p7 ∧ p5) → (p7 ∨ p3)) → ((p1 ∨ p6) → False))) ∨ ((((p5 ∨ p4) ∧ (p6 ∧ p0)) → ((p3 → False) → False)) ∨ (((p7 ∨ p2) ∨ (p2 ∨ p0)) ∨ ((p4 → False) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  have assump_11 : (True ∨ p0) := by
    apply Or.inl
    apply True.intro
  let assump_7 := assump_1 assump_11
  apply False.elim assump_7


variable (p1 p0 p3 p7 p4 p2 p6 : Prop)
theorem file97_72804 : (((((p0 ∨ p1) ∧ (p7 → False)) ∧ ((p2 → False) → (p0 ∧ p6))) ∧ (((p3 → p4) → (p1 ∨ p3)) ∧ ((p6 ∨ True) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_3
          case intro assump_16 assump_17 =>
            have assump_42 : (p6 ∨ True) := by
              apply Or.inr
              apply True.intro
            let assump_22 := assump_17 assump_42
            apply False.elim assump_22
        case inr assump_9 =>
          cases assump_3
          case intro assump_32 assump_33 =>
            have assump_43 : (p6 ∨ True) := by
              apply Or.inr
              apply True.intro
            let assump_38 := assump_33 assump_43
            apply False.elim assump_38


variable (p2 p1 p3 p7 p6 p0 p5 : Prop)
theorem file97_73782 : (((((p6 → p6) → False) → False) ∧ (((True ∧ p3) → False) ∧ ((False ∧ p3) → (p2 ∧ p3)))) → ((((p3 ∧ p5) ∧ (p5 ∧ p0)) ∧ ((p7 → p6) → (False → p1))) → False)) := by
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
          cases assump_1
          case intro assump_21 assump_22 =>
            cases assump_22
            case intro assump_25 assump_26 =>
              have assump_36 : (True ∧ p3) := by
                apply And.intro
                apply True.intro
                exact assump_7
              let assump_32 := assump_25 assump_36
              apply False.elim assump_32


variable (p3 p5 p2 p7 p4 p1 p6 : Prop)
theorem file97_74651 : ((((((p1 ∧ p3) ∨ (p1 ∧ p2)) → ((p1 → False) ∧ (p2 → p5))) ∨ (((p4 → False) ∧ (p6 ∨ p3)) → ((False → p1) ∨ (True ∧ p5)))) ∧ ((((p3 → True) ∨ (p1 ∧ p2)) → False) ∧ (((False ∧ p1) → False) ∧ ((p7 → False) ∨ (p6 → p2))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          cases assump_13
          case inl assump_16 =>
            have assump_66 : ((p3 → True) ∨ (p1 ∧ p2)) := by
              apply Or.inl
              intro assump_23
              apply True.intro
            let assump_22 := assump_8 assump_66
            apply False.elim assump_22
          case inr assump_17 =>
            have assump_67 : ((p3 → True) ∨ (p1 ∧ p2)) := by
              apply Or.inl
              intro assump_32
              apply True.intro
            let assump_31 := assump_8 assump_67
            apply False.elim assump_31
    case inr assump_5 =>
      cases assump_3
      case intro assump_38 assump_39 =>
        cases assump_39
        case intro assump_42 assump_43 =>
          cases assump_43
          case inl assump_46 =>
            have assump_68 : ((p3 → True) ∨ (p1 ∧ p2)) := by
              apply Or.inl
              intro assump_53
              apply True.intro
            let assump_52 := assump_38 assump_68
            apply False.elim assump_52
          case inr assump_47 =>
            have assump_69 : ((p3 → True) ∨ (p1 ∧ p2)) := by
              apply Or.inl
              intro assump_62
              apply True.intro
            let assump_61 := assump_38 assump_69
            apply False.elim assump_61


variable (p1 p5 p2 p3 p6 p4 p0 p7 : Prop)
theorem file97_76464 : ((((((False → p4) ∧ (p7 ∨ p2)) ∨ ((True ∧ p5) → False)) → (((True → p1) → (False ∨ False)) ∧ ((p2 → True) → False))) ∧ ((((p1 → p3) ∨ (p6 ∨ True)) → False) ∧ (((p4 → p4) ∨ (p4 ∨ p0)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_19 : ((p4 → p4) ∨ (p4 ∨ p0)) := by
        apply Or.inl
        intro assump_13
        exact assump_13
      let assump_12 := assump_7 assump_19
      apply False.elim assump_12


variable (p6 p5 p4 p7 p1 p3 p0 : Prop)
theorem file97_77056 : ((((((p7 ∧ p0) → (p4 → False)) → ((p6 ∨ p5) → False)) → (((p3 ∨ p6) ∨ (p3 → False)) ∨ ((False → False) ∧ (p1 ∧ p1)))) ∧ ((((p6 → False) → False) → False) ∧ (((p5 ∨ True) ∧ (False → p0)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_19 : ((p5 ∨ True) ∧ (False → p0)) := by
        apply And.intro
        apply Or.inr
        apply True.intro
        intro assump_13
        apply False.elim assump_13
      let assump_12 := assump_7 assump_19
      apply False.elim assump_12


variable (p3 p7 p4 p1 p2 p5 p0 : Prop)
theorem file97_77716 : (((((True ∨ p7) ∨ (True ∨ p1)) ∨ ((p3 → p5) ∨ (p2 ∨ p4))) ∨ (((p0 ∨ p3) ∧ (False ∨ True)) ∨ ((p5 → False) → False))) ∨ ((((p4 ∨ p5) → (p2 ∧ False)) → ((p4 ∨ True) ∨ (False → False))) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply True.intro


variable (p3 p1 p6 p2 p5 p7 p4 : Prop)
theorem file97_78072 : ((((((p2 → True) ∨ (p7 ∧ p4)) ∨ ((p6 → False) ∧ (p1 ∨ False))) → False) ∧ ((((p6 ∨ p3) ∨ (p2 ∨ p3)) → False) ∨ (((p2 ∨ p5) ∧ (False → False)) → ((True ∧ p3) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      have assump_24 : (((p2 → True) ∨ (p7 ∧ p4)) ∨ ((p6 → False) ∧ (p1 ∨ False))) := by
        apply Or.inl
        apply Or.inl
        intro assump_12
        apply True.intro
      let assump_11 := assump_2 assump_24
      apply False.elim assump_11
    case inr assump_7 =>
      have assump_25 : (((p2 → True) ∨ (p7 ∧ p4)) ∨ ((p6 → False) ∧ (p1 ∨ False))) := by
        apply Or.inl
        apply Or.inl
        intro assump_20
        apply True.intro
      let assump_19 := assump_2 assump_25
      apply False.elim assump_19


variable (p5 p1 p3 p4 p6 p2 p7 : Prop)
theorem file97_78966 : (((((False → False) → False) ∧ ((p1 → False) ∧ (p1 ∧ p2))) ∧ (((p5 ∧ p5) ∧ (p3 ∨ False)) → False)) → ((((p2 → False) ∧ (p1 ∨ False)) → False) ∨ (((p5 ∧ p6) ∨ (p7 ∧ p1)) → ((p3 → False) → (p4 ∧ True))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          apply Or.inl
          intro assump_20
          cases assump_20
          case intro assump_21 assump_22 =>
            cases assump_22
            case inl assump_25 =>
              have assump_36 : p2 := by
                exact assump_13
              let assump_30 := assump_21 assump_36
              apply False.elim assump_30
            case inr assump_26 =>
              apply False.elim assump_26


variable (p3 p6 p5 p7 p1 : Prop)
theorem file97_79899 : (((((p1 ∧ p6) → (p1 → True)) ∨ ((p5 → False) ∨ (p1 ∧ True))) ∨ (((p7 → p5) ∧ (p3 ∧ p6)) → False)) ∨ ((((p3 ∨ False) → False) → False) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_5
  intro assump_6
  apply True.intro


variable (p7 p6 p3 p4 p1 : Prop)
theorem file97_80204 : ((((((p3 → False) → False) → ((p1 ∧ p7) ∨ (p3 → False))) → (((p4 ∧ p7) → (p3 → True)) ∨ ((False ∨ p6) → False))) → False) → False) := by
  intro assump_1
  have assump_13 : ((((p3 → False) → False) → ((p1 ∧ p7) ∨ (p3 → False))) → (((p4 ∧ p7) → (p3 → True)) ∨ ((False ∨ p6) → False))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    intro assump_9
    apply True.intro
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p5 p7 p6 p1 p0 : Prop)
theorem file97_80711 : (((((True ∨ p5) → False) ∧ ((p1 ∨ p7) → False)) → (((p5 ∨ p6) ∨ (p0 → True)) ∧ ((p5 ∧ False) ∨ (p1 ∨ p5)))) ∨ ((((p1 ∧ False) ∧ (p7 ∨ p5)) → ((False → p1) ∧ (p1 → p5))) → (((p1 ∨ p6) ∧ (p1 ∧ False)) → False))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inr
    intro assump_8
    apply True.intro
  cases assump_1
  case intro assump_9 assump_10 =>
    have assump_20 : (True ∨ p5) := by
      apply Or.inl
      apply True.intro
    let assump_16 := assump_9 assump_20
    apply False.elim assump_16


variable (p4 p1 p2 p5 : Prop)
theorem file97_81343 : ((((((p5 ∧ p4) → (p2 ∨ p4)) → False) → (((p1 → False) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_25 : ((((p5 ∧ p4) → (p2 ∨ p4)) → False) → (((p1 → False) → False) → False)) := by
    intro assump_5
    intro assump_6
    have assump_26 : ((p5 ∧ p4) → (p2 ∨ p4)) := by
      intro assump_12
      cases assump_12
      case intro assump_13 assump_14 =>
        apply Or.inr
        exact assump_14
    let assump_11 := assump_5 assump_26
    apply False.elim assump_11
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p5 p6 p2 p4 : Prop)
theorem file97_81961 : ((((((p5 ∨ p4) ∨ (True → False)) ∧ ((True → False) ∧ (p2 ∧ p6))) → False) → False) → False) := by
  intro assump_1
  have assump_69 : ((((p5 ∨ p4) ∨ (True → False)) ∧ ((True → False) ∧ (p2 ∧ p6))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_7
          case intro assump_14 assump_15 =>
            cases assump_15
            case intro assump_18 assump_19 =>
              have assump_70 : True := by
                apply True.intro
              let assump_26 := assump_14 assump_70
              apply False.elim assump_26
        case inr assump_11 =>
          cases assump_7
          case intro assump_32 assump_33 =>
            cases assump_33
            case intro assump_36 assump_37 =>
              have assump_71 : True := by
                apply True.intro
              let assump_44 := assump_32 assump_71
              apply False.elim assump_44
      case inr assump_9 =>
        cases assump_7
        case intro assump_50 assump_51 =>
          cases assump_51
          case intro assump_54 assump_55 =>
            have assump_72 : True := by
              apply True.intro
            let assump_62 := assump_50 assump_72
            apply False.elim assump_62
  let assump_4 := assump_1 assump_69
  apply False.elim assump_4


variable (p5 p1 p4 p2 p0 : Prop)
theorem file97_83441 : (((((p0 → False) → (p2 ∧ False)) ∨ ((p5 → False) ∨ (False ∨ True))) ∧ (((p4 → p4) → False) ∧ ((p1 ∨ p4) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        have assump_60 : (p4 → p4) := by
          intro assump_16
          exact assump_16
        let assump_15 := assump_8 assump_60
        apply False.elim assump_15
    case inr assump_5 =>
      cases assump_5
      case inl assump_22 =>
        cases assump_3
        case intro assump_26 assump_27 =>
          have assump_61 : (p4 → p4) := by
            intro assump_34
            exact assump_34
          let assump_33 := assump_26 assump_61
          apply False.elim assump_33
      case inr assump_23 =>
        cases assump_23
        case inl assump_40 =>
          apply False.elim assump_40
        case inr assump_41 =>
          cases assump_3
          case intro assump_46 assump_47 =>
            have assump_62 : (p4 → p4) := by
              intro assump_54
              exact assump_54
            let assump_53 := assump_46 assump_62
            apply False.elim assump_53


variable (p0 p1 p7 p6 p2 : Prop)
theorem file97_84704 : ((((((p1 → False) → (p0 → False)) ∧ ((p7 → False) ∧ (p2 → False))) → (((p6 → False) ∧ (p0 ∧ p2)) → False)) → False) → False) := by
  intro assump_1
  have assump_34 : ((((p1 → False) → (p0 → False)) ∧ ((p7 → False) ∧ (p2 → False))) → (((p6 → False) ∧ (p0 ∧ p2)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        cases assump_5
        case intro assump_17 assump_18 =>
          cases assump_18
          case intro assump_21 assump_22 =>
            have assump_35 : p2 := by
              exact assump_12
            let assump_27 := assump_22 assump_35
            apply False.elim assump_27
  let assump_4 := assump_1 assump_34
  apply False.elim assump_4


variable (p7 p2 p5 p3 p0 p4 p6 p1 : Prop)
theorem file97_85558 : (((((p3 → False) ∧ (p2 ∧ p7)) ∧ ((p5 → p1) ∨ (p4 → False))) → False) → ((((True → False) ∧ (p5 → False)) → False) ∨ (((p1 ∧ True) ∨ (p4 → p6)) ∨ ((p0 ∨ p0) → (False → False))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    have assump_16 : True := by
      apply True.intro
    let assump_12 := assump_5 assump_16
    apply False.elim assump_12


variable (p4 p6 p3 p5 p7 p1 p2 : Prop)
theorem file97_86031 : ((((((p7 → False) ∧ (p3 ∧ True)) → ((True ∧ p4) ∨ (p7 → p5))) ∨ (((p3 → False) ∨ (p6 ∨ p2)) ∧ ((p6 ∧ p1) → (p7 ∨ p3)))) → False) → False) := by
  intro assump_5
  have assump_32 : ((((p7 → False) ∧ (p3 ∧ True)) → ((True ∧ p4) ∨ (p7 → p5))) ∨ (((p3 → False) ∨ (p6 ∨ p2)) ∧ ((p6 ∧ p1) → (p7 ∨ p3)))) := by
    apply Or.inl
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      cases assump_11
      case intro assump_14 assump_15 =>
        apply Or.inr
        intro assump_20
        have assump_33 : p7 := by
          exact assump_20
        let assump_25 := assump_10 assump_33
        apply False.elim assump_25
  let assump_8 := assump_5 assump_32
  apply False.elim assump_8


variable (p3 p7 p2 p1 p6 p5 : Prop)
theorem file97_86800 : (((((p5 → p3) → (p3 → p1)) → ((p7 → p3) → False)) ∧ (((p7 ∨ p6) → (p2 → False)) ∧ ((p7 ∧ True) → False))) → ((((p7 ∧ p1) → False) ∨ ((True ∧ p2) ∨ (p6 → True))) ∨ (((p6 → False) ∨ (p1 ∧ False)) → ((p2 ∧ False) ∨ (p2 → True))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      apply Or.inl
      apply Or.inl
      intro assump_12
      cases assump_12
      case intro assump_13 assump_14 =>
        have assump_25 : (p7 ∧ True) := by
          apply And.intro
          exact assump_13
          apply True.intro
        let assump_21 := assump_7 assump_25
        apply False.elim assump_21


variable (p2 p4 p6 p0 p3 p5 p7 p1 : Prop)
theorem file97_87546 : (((((p2 ∧ p6) → (p7 → p1)) → ((True → False) → (p6 ∨ True))) ∨ (((p5 ∧ p6) → (p6 ∨ p6)) → ((True ∨ p5) → (False ∧ False)))) ∨ ((((p0 ∨ False) → (p3 ∧ False)) ∨ ((True → False) → (p3 → False))) ∧ (((p6 ∧ p3) ∧ (p4 → p4)) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  apply Or.inr
  apply True.intro


variable (p2 p3 p4 p7 p1 p6 p5 : Prop)
theorem file97_87944 : (((((p3 ∧ True) → (p1 → False)) ∧ ((True → p2) ∨ (p2 ∧ p4))) → (((False → False) ∨ (p6 ∨ p6)) ∨ ((p5 → p5) ∧ (p5 → False)))) ∨ ((((p3 → False) → (p7 → p7)) ∨ ((True ∨ p3) ∧ (False → p2))) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      apply Or.inl
      apply Or.inl
      intro assump_10
      apply False.elim assump_10
    case inr assump_7 =>
      cases assump_7
      case intro assump_13 assump_14 =>
        apply Or.inl
        apply Or.inl
        intro assump_19
        apply False.elim assump_19


variable (p4 p1 p6 p5 p7 p3 : Prop)
theorem file97_88615 : ((((((p6 ∧ p4) ∨ (True ∨ p3)) ∨ ((p3 ∧ False) → (p5 ∧ p6))) ∨ (((True ∧ p1) ∧ (True ∨ p7)) ∧ ((p5 ∨ p5) ∧ (False ∧ p1)))) → False) → False) := by
  intro assump_1
  have assump_8 : ((((p6 ∧ p4) ∨ (True ∨ p3)) ∨ ((p3 ∧ False) → (p5 ∧ p6))) ∨ (((True ∧ p1) ∧ (True ∨ p7)) ∧ ((p5 ∨ p5) ∧ (False ∧ p1)))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p3 p2 p1 p0 p6 : Prop)
theorem file97_89132 : ((((((True ∨ False) → False) → False) ∨ (((p2 ∨ False) ∧ (p1 → False)) → ((p6 ∧ False) ∧ (p3 ∧ p0)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((True ∨ False) → False) → False) ∨ (((p2 ∨ False) ∧ (p1 → False)) → ((p6 ∧ False) ∧ (p3 ∧ p0)))) := by
    apply Or.inl
    intro assump_5
    have assump_16 : (True ∨ False) := by
      apply Or.inl
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p4 p6 p3 p5 p0 p2 p1 p7 : Prop)
theorem file97_89720 : ((((((p7 → p6) ∨ (p7 → False)) ∨ ((p1 ∧ False) ∨ (False ∧ p0))) → (((p0 → p3) → (True ∨ False)) ∨ ((p4 ∧ p2) → (True ∨ p5)))) → ((((p3 ∨ p6) → False) → ((p6 ∨ p6) → (p1 → p2))) → False)) → False) := by
  intro assump_1
  have assump_59 : ((((p7 → p6) ∨ (p7 → False)) ∨ ((p1 ∧ False) ∨ (False ∧ p0))) → (((p0 → p3) → (True ∨ False)) ∨ ((p4 ∧ p2) → (True ∨ p5)))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        apply Or.inl
        intro assump_12
        apply Or.inl
        apply True.intro
      case inr assump_9 =>
        apply Or.inl
        intro assump_17
        apply Or.inl
        apply True.intro
    case inr assump_7 =>
      cases assump_7
      case inl assump_20 =>
        cases assump_20
        case intro assump_22 assump_23 =>
          apply False.elim assump_23
      case inr assump_21 =>
        cases assump_21
        case intro assump_28 assump_29 =>
          apply False.elim assump_28
  let assump_4 := assump_1 assump_59
  have assump_60 : (((p3 ∨ p6) → False) → ((p6 ∨ p6) → (p1 → p2))) := by
    intro assump_33
    intro assump_34
    intro assump_35
    cases assump_34
    case inl assump_38 =>
      have assump_61 : (p3 ∨ p6) := by
        apply Or.inr
        exact assump_38
      let assump_44 := assump_33 assump_61
      apply False.elim assump_44
    case inr assump_39 =>
      have assump_62 : (p3 ∨ p6) := by
        apply Or.inr
        exact assump_39
      let assump_52 := assump_33 assump_62
      apply False.elim assump_52
  let assump_32 := assump_4 assump_60
  apply False.elim assump_32


variable (p4 p2 : Prop)
theorem file97_91393 : ((((((p4 ∨ p2) ∨ (p2 → False)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_23 : ((((p4 ∨ p2) ∨ (p2 → False)) → False) → False) := by
    intro assump_5
    have assump_24 : ((p4 ∨ p2) ∨ (p2 → False)) := by
      apply Or.inr
      intro assump_9
      have assump_25 : ((p4 ∨ p2) ∨ (p2 → False)) := by
        apply Or.inl
        apply Or.inr
        exact assump_9
      let assump_13 := assump_5 assump_25
      apply False.elim assump_13
    let assump_8 := assump_5 assump_24
    apply False.elim assump_8
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p2 p7 p3 p4 p6 p1 : Prop)
theorem file97_92058 : (((((False ∧ p4) → False) → ((p4 → p4) ∧ (p6 ∨ p1))) ∧ (((p7 → p3) ∨ (p4 ∨ p6)) ∧ ((p2 ∧ False) ∧ (True ∨ p6)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            apply False.elim assump_15
      case inr assump_9 =>
        cases assump_9
        case inl assump_20 =>
          cases assump_7
          case intro assump_24 assump_25 =>
            cases assump_24
            case intro assump_26 assump_27 =>
              apply False.elim assump_27
        case inr assump_21 =>
          cases assump_7
          case intro assump_34 assump_35 =>
            cases assump_34
            case intro assump_36 assump_37 =>
              apply False.elim assump_37


variable (p0 p5 p7 : Prop)
theorem file97_93060 : ((((((False ∨ False) ∧ (p0 ∧ p7)) → False) ∨ (((False → False) ∨ (p5 → False)) ∧ ((True → False) → (p0 → False)))) → False) → False) := by
  intro assump_1
  have assump_17 : ((((False ∨ False) ∧ (p0 ∧ p7)) → False) ∨ (((False → False) ∨ (p5 → False)) ∧ ((True → False) → (p0 → False)))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        apply False.elim assump_8
      case inr assump_9 =>
        apply False.elim assump_9
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p3 p2 p7 p0 p1 : Prop)
theorem file97_93710 : ((((((p3 → p7) ∧ (True ∨ p2)) → False) → (((p1 → True) ∧ (True → False)) → ((False ∨ p0) → (p7 → False)))) → False) → False) := by
  intro assump_1
  have assump_35 : ((((p3 → p7) ∧ (True ∨ p2)) → False) → (((p1 → True) ∧ (True → False)) → ((False ∨ p0) → (p7 → False)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    cases assump_7
    case inl assump_11 =>
      apply False.elim assump_11
    case inr assump_12 =>
      cases assump_6
      case intro assump_17 assump_18 =>
        have assump_36 : ((p3 → p7) ∧ (True ∨ p2)) := by
          apply And.intro
          intro assump_26
          exact assump_8
          apply Or.inl
          apply True.intro
        let assump_25 := assump_5 assump_36
        apply False.elim assump_25
  let assump_4 := assump_1 assump_35
  apply False.elim assump_4


variable (p3 p5 p7 p0 p1 : Prop)
theorem file97_94614 : ((((((p7 ∧ False) ∧ (p5 ∧ p7)) ∨ ((False ∧ p1) → (p1 ∨ True))) ∨ (((p5 → False) → (p3 ∧ p0)) → ((True → p5) ∧ (p1 ∧ False)))) → False) → False) := by
  intro assump_1
  have assump_13 : ((((p7 ∧ False) ∧ (p5 ∧ p7)) ∨ ((False ∧ p1) → (p1 ∨ True))) ∨ (((p5 → False) → (p3 ∧ p0)) → ((True → p5) ∧ (p1 ∧ False)))) := by
    apply Or.inl
    apply Or.inr
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p3 p2 p7 p5 p0 p4 p1 : Prop)
theorem file97_95198 : (((((p0 → p5) ∧ (p5 → False)) ∧ ((False ∧ p4) → False)) → (((p2 ∧ p5) ∧ (p4 → False)) → ((p0 ∨ p3) → (p5 ∨ p4)))) ∨ ((((p0 → p7) ∧ (p5 ∧ p3)) → False) ∧ (((p1 ∧ p5) ∨ (p4 → False)) → False))) := by
  apply Or.inl
  intro assump_29
  intro assump_30
  intro assump_31
  cases assump_31
  case inl assump_32 =>
    cases assump_30
    case intro assump_36 assump_37 =>
      cases assump_36
      case intro assump_38 assump_39 =>
        cases assump_29
        case intro assump_46 assump_47 =>
          cases assump_46
          case intro assump_48 assump_49 =>
            apply Or.inl
            exact assump_39
  case inr assump_33 =>
    cases assump_30
    case intro assump_58 assump_59 =>
      cases assump_58
      case intro assump_60 assump_61 =>
        cases assump_29
        case intro assump_68 assump_69 =>
          cases assump_68
          case intro assump_70 assump_71 =>
            apply Or.inl
            exact assump_61


variable (p1 p6 p3 p5 p4 p0 p2 : Prop)
theorem file97_96212 : (((((p5 ∨ True) → False) ∧ ((p3 → p4) ∨ (p5 ∨ False))) → False) ∨ ((((True → p6) → False) ∨ ((False → p3) ∧ (p1 ∨ p3))) ∧ (((p1 → p0) ∧ (p2 → p3)) ∨ ((p2 → p0) ∧ (p1 → p3))))) := by
  apply Or.inl
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_7
    case inl assump_10 =>
      have assump_30 : (p5 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_15 := assump_6 assump_30
      apply False.elim assump_15
    case inr assump_11 =>
      cases assump_11
      case inl assump_19 =>
        have assump_31 : (p5 ∨ True) := by
          apply Or.inl
          exact assump_19
        let assump_24 := assump_6 assump_31
        apply False.elim assump_24
      case inr assump_20 =>
        apply False.elim assump_20


variable (p7 p5 p6 p4 : Prop)
theorem file97_97048 : (((((p4 ∧ p5) → (True ∨ p7)) → ((False → False) ∨ (p6 ∧ p5))) → False) → False) := by
  intro assump_1
  have assump_14 : (((p4 ∧ p5) → (True ∨ p7)) → ((False → False) ∨ (p6 ∧ p5))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p3 p0 p1 p6 p7 p5 p4 : Prop)
theorem file97_97449 : (((((p0 → p6) → (p3 → False)) → False) ∧ (((True ∨ p1) ∧ (p6 → False)) ∨ ((p5 ∨ True) → (p6 ∧ p4)))) → ((((p4 → p3) → False) → False) → (((p1 ∧ p7) ∧ (p7 ∧ False)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_4
    case intro assump_6 assump_7 =>
      cases assump_5
      case intro assump_12 assump_13 =>
        apply False.elim assump_13


variable (p6 p4 p1 p7 p0 : Prop)
theorem file97_97940 : (((((p1 → p1) ∨ (True ∧ p4)) → False) → False) ∨ ((((p0 ∧ p4) → (p1 → p7)) → ((p6 → False) ∧ (True → False))) ∨ (((p7 → p0) ∧ (p1 ∨ p0)) → False))) := by
  apply Or.inl
  intro assump_1
  have assump_11 : ((p1 → p1) ∨ (True ∧ p4)) := by
    apply Or.inl
    intro assump_5
    exact assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p5 p6 p3 : Prop)
theorem file97_98348 : ((((((p3 → False) → False) ∧ ((p6 → False) ∧ (p5 ∧ False))) → False) → False) → False) := by
  intro assump_1
  have assump_23 : ((((p3 → False) → False) ∧ ((p6 → False) ∧ (p5 ∧ False))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          apply False.elim assump_15
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p4 p3 p6 p2 p7 p5 p1 p0 : Prop)
theorem file97_98919 : (((((p0 ∨ p3) ∨ (False → p5)) ∨ ((p3 → p4) → False)) ∨ (((p6 ∨ p7) ∧ (p7 ∧ p1)) → False)) ∨ ((((p4 ∨ p7) → False) → ((p3 ∧ p2) → False)) ∨ (((p5 ∧ True) → (p7 → p2)) → ((p0 ∨ p0) → (True ∨ p3))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inr
  intro assump_1
  apply False.elim assump_1


variable (p3 p0 p7 p2 p5 : Prop)
theorem file97_99284 : (((((p3 → False) → (p3 → p7)) → False) ∧ (((p2 → p2) → (p3 → p5)) ∧ ((False ∨ p0) ∧ (p2 → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          apply False.elim assump_12
        case inr assump_13 =>
          have assump_41 : ((p3 → False) → (p3 → p7)) := by
            intro assump_28
            intro assump_29
            have assump_42 : p3 := by
              exact assump_29
            let assump_34 := assump_28 assump_42
            apply False.elim assump_34
          let assump_27 := assump_2 assump_41
          apply False.elim assump_27


variable (p0 p6 p4 p1 p2 : Prop)
theorem file97_100116 : (((((p2 ∨ p0) → False) → False) ∧ (((p4 ∧ p0) ∨ (p2 → False)) ∧ ((p6 ∧ False) ∧ (True ∧ p1)))) → False) := by
  intro assump_13
  cases assump_13
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


variable (p4 p1 p6 p0 p5 : Prop)
theorem file97_100917 : (((((True ∨ False) ∨ (p1 ∨ p5)) → False) → False) ∨ ((((p1 → False) → (True ∨ True)) → ((p6 → p4) ∧ (p1 ∨ p5))) ∨ (((True ∧ p4) ∨ (p4 → False)) ∧ ((p6 ∧ p0) → False)))) := by
  apply Or.inl
  intro assump_1
  have assump_8 : ((True ∨ False) ∨ (p1 ∨ p5)) := by
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p7 p6 p1 p5 p3 p4 : Prop)
theorem file97_101356 : ((((((p1 → p7) → (p6 ∧ p7)) → False) → (((p6 ∧ True) ∨ (p7 ∨ p4)) ∧ ((p5 ∧ True) → (False ∨ p3)))) ∧ ((((False → True) → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_20 : (((False → True) → False) → False) := by
      intro assump_9
      have assump_21 : (False → True) := by
        intro assump_13
        apply True.intro
      let assump_12 := assump_9 assump_21
      apply False.elim assump_12
    let assump_8 := assump_3 assump_20
    apply False.elim assump_8


variable (p1 p0 : Prop)
theorem file97_101954 : (((((False → False) → (p0 ∧ False)) → ((True ∧ p1) ∧ (True → True))) → False) → False) := by
  intro assump_1
  have assump_21 : (((False → False) → (p0 ∧ False)) → ((True ∧ p1) ∧ (True → True))) := by
    intro assump_5
    apply And.intro
    apply And.intro
    apply True.intro
    have assump_22 : (False → False) := by
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_22
    let assump_12 := And.right assump_8
    apply False.elim assump_12
    intro assump_17
    apply True.intro
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p7 p2 p6 p5 p3 : Prop)
theorem file97_102605 : (((((p2 → False) ∧ (False ∧ p3)) ∧ ((p2 ∧ p3) ∧ (False → p5))) ∧ (((p7 ∨ p6) → (p5 → p7)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          apply False.elim assump_10


variable (p2 p7 p3 p0 p1 : Prop)
theorem file97_103061 : ((((((p0 ∨ p1) ∨ (p1 ∨ p1)) ∧ ((False ∨ p2) ∧ (p1 → False))) ∧ (((p2 ∧ p1) ∧ (p7 → False)) → False)) ∧ ((((p2 ∧ False) ∧ (p7 ∧ p3)) ∨ ((p1 ∨ p2) ∨ (False ∨ False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_8
          case inl assump_10 =>
            cases assump_7
            case intro assump_14 assump_15 =>
              cases assump_14
              case inl assump_16 =>
                apply False.elim assump_16
              case inr assump_17 =>
                have assump_94 : (((p2 ∧ False) ∧ (p7 ∧ p3)) ∨ ((p1 ∨ p2) ∨ (False ∨ False))) := by
                  apply Or.inr
                  apply Or.inl
                  apply Or.inr
                  exact assump_17
                let assump_28 := assump_3 assump_94
                apply False.elim assump_28
          case inr assump_11 =>
            cases assump_7
            case intro assump_34 assump_35 =>
              cases assump_34
              case inl assump_36 =>
                apply False.elim assump_36
              case inr assump_37 =>
                have assump_95 : (((p2 ∧ False) ∧ (p7 ∧ p3)) ∨ ((p1 ∨ p2) ∨ (False ∨ False))) := by
                  apply Or.inr
                  apply Or.inl
                  apply Or.inl
                  exact assump_11
                let assump_48 := assump_3 assump_95
                apply False.elim assump_48
        case inr assump_9 =>
          cases assump_9
          case inl assump_52 =>
            cases assump_7
            case intro assump_56 assump_57 =>
              cases assump_56
              case inl assump_58 =>
                apply False.elim assump_58
              case inr assump_59 =>
                have assump_96 : (((p2 ∧ False) ∧ (p7 ∧ p3)) ∨ ((p1 ∨ p2) ∨ (False ∨ False))) := by
                  apply Or.inr
                  apply Or.inl
                  apply Or.inl
                  exact assump_52
                let assump_70 := assump_3 assump_96
                apply False.elim assump_70
          case inr assump_53 =>
            cases assump_7
            case intro assump_76 assump_77 =>
              cases assump_76
              case inl assump_78 =>
                apply False.elim assump_78
              case inr assump_79 =>
                have assump_97 : (((p2 ∧ False) ∧ (p7 ∧ p3)) ∨ ((p1 ∨ p2) ∨ (False ∨ False))) := by
                  apply Or.inr
                  apply Or.inl
                  apply Or.inl
                  exact assump_53
                let assump_90 := assump_3 assump_97
                apply False.elim assump_90


variable (p7 p3 : Prop)
theorem file97_105900 : (((((p3 ∧ p3) → False) → ((p3 → False) ∨ (p7 → False))) → False) → False) := by
  intro assump_1
  have assump_19 : (((p3 ∧ p3) → False) → ((p3 → False) ∨ (p7 → False))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    have assump_20 : (p3 ∧ p3) := by
      apply And.intro
      exact assump_8
      exact assump_8
    let assump_12 := assump_5 assump_20
    apply False.elim assump_12
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p3 p1 p5 p6 p0 p4 : Prop)
theorem file97_106428 : ((((((p3 → p3) ∧ (True ∧ p0)) → ((p5 ∧ p1) → False)) → False) ∧ ((((p0 ∧ p6) ∧ (p5 → p1)) → ((False ∧ p1) → (p4 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_21 : (((p0 ∧ p6) ∧ (p5 → p1)) → ((False ∧ p1) → (p4 → False))) := by
      intro assump_9
      intro assump_10
      intro assump_11
      cases assump_10
      case intro assump_14 assump_15 =>
        apply False.elim assump_14
    let assump_8 := assump_3 assump_21
    apply False.elim assump_8


variable (p0 p1 p3 p4 p7 p5 p6 : Prop)
theorem file97_107023 : (((((p5 → False) → (p5 ∧ p3)) → False) → False) → ((((False → False) ∧ (False ∧ True)) → ((p7 ∧ p6) ∨ (p1 ∨ p6))) ∨ (((p4 → False) ∧ (p5 ∧ p1)) ∨ ((p3 → p3) → (p0 → False))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      apply False.elim assump_9


variable (p6 p3 p5 p4 p1 p7 p0 p2 : Prop)
theorem file97_107459 : ((((((p6 → p5) ∧ (True ∧ p1)) ∨ ((p0 ∧ p1) ∧ (p4 → p3))) → (((True → False) ∧ (True ∧ p2)) → False)) ∧ ((((p4 ∨ False) ∧ (False ∧ p1)) → ((p7 ∧ p4) ∨ (False → p7))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_25 : (((p4 ∨ False) ∧ (False ∧ p1)) → ((p7 ∧ p4) ∨ (False → p7))) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          cases assump_11
          case intro assump_16 assump_17 =>
            apply False.elim assump_16
        case inr assump_13 =>
          apply False.elim assump_13
    let assump_8 := assump_3 assump_25
    apply False.elim assump_8


variable (p4 p0 p5 p6 p2 : Prop)
theorem file97_108243 : ((((((True → False) → False) ∨ ((False ∨ p6) ∨ (True → p5))) ∨ (((p0 → False) → (p2 ∨ p2)) ∧ ((p5 ∨ p2) ∧ (p6 ∧ p4)))) → False) → False) := by
  intro assump_9
  have assump_23 : ((((True → False) → False) ∨ ((False ∨ p6) ∨ (True → p5))) ∨ (((p0 → False) → (p2 ∨ p2)) ∧ ((p5 ∨ p2) ∧ (p6 ∧ p4)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_13
    have assump_24 : True := by
      apply True.intro
    let assump_16 := assump_13 assump_24
    apply False.elim assump_16
  let assump_12 := assump_9 assump_23
  apply False.elim assump_12


