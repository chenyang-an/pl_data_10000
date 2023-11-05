variable (p5 p4 p2 p1 p6 p0 p3 p7 : Prop)
theorem file36_50 : (((((p4 → False) → False) ∨ ((True ∨ p1) → False)) ∧ (((p6 ∨ False) ∧ (False → p2)) ∧ ((p0 → p7) ∧ (p3 ∧ p5)))) → ((((p7 ∧ p6) → False) ∧ ((p7 → p2) ∨ (p4 → p3))) → (((p6 ∧ False) ∧ (False → p6)) ∨ ((p3 ∨ p4) → (p7 ∨ p5))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case inl assump_7 =>
      cases assump_1
      case intro assump_11 assump_12 =>
        cases assump_11
        case inl assump_13 =>
          cases assump_12
          case intro assump_17 assump_18 =>
            cases assump_17
            case intro assump_19 assump_20 =>
              cases assump_19
              case inl assump_21 =>
                cases assump_18
                case intro assump_27 assump_28 =>
                  cases assump_28
                  case intro assump_31 assump_32 =>
                    apply Or.inr
                    intro assump_37
                    cases assump_37
                    case inl assump_38 =>
                      apply Or.inr
                      exact assump_32
                    case inr assump_39 =>
                      apply Or.inr
                      exact assump_32
              case inr assump_22 =>
                apply False.elim assump_22
        case inr assump_14 =>
          cases assump_12
          case intro assump_48 assump_49 =>
            cases assump_48
            case intro assump_50 assump_51 =>
              cases assump_50
              case inl assump_52 =>
                cases assump_49
                case intro assump_58 assump_59 =>
                  cases assump_59
                  case intro assump_62 assump_63 =>
                    apply Or.inr
                    intro assump_68
                    cases assump_68
                    case inl assump_69 =>
                      apply Or.inr
                      exact assump_63
                    case inr assump_70 =>
                      apply Or.inr
                      exact assump_63
              case inr assump_53 =>
                apply False.elim assump_53
    case inr assump_8 =>
      cases assump_1
      case intro assump_79 assump_80 =>
        cases assump_79
        case inl assump_81 =>
          cases assump_80
          case intro assump_85 assump_86 =>
            cases assump_85
            case intro assump_87 assump_88 =>
              cases assump_87
              case inl assump_89 =>
                cases assump_86
                case intro assump_95 assump_96 =>
                  cases assump_96
                  case intro assump_99 assump_100 =>
                    apply Or.inr
                    intro assump_105
                    cases assump_105
                    case inl assump_106 =>
                      apply Or.inr
                      exact assump_100
                    case inr assump_107 =>
                      apply Or.inr
                      exact assump_100
              case inr assump_90 =>
                apply False.elim assump_90
        case inr assump_82 =>
          cases assump_80
          case intro assump_116 assump_117 =>
            cases assump_116
            case intro assump_118 assump_119 =>
              cases assump_118
              case inl assump_120 =>
                cases assump_117
                case intro assump_126 assump_127 =>
                  cases assump_127
                  case intro assump_130 assump_131 =>
                    apply Or.inr
                    intro assump_136
                    cases assump_136
                    case inl assump_137 =>
                      apply Or.inr
                      exact assump_131
                    case inr assump_138 =>
                      apply Or.inr
                      exact assump_131
              case inr assump_121 =>
                apply False.elim assump_121


variable (p6 p2 p7 p4 p0 p1 : Prop)
theorem file36_3981 : (((((p6 ∧ False) → False) → ((True → p4) ∨ (p6 → True))) → False) → ((((p7 → False) → (p2 ∨ p1)) → ((p4 ∨ p2) ∨ (False → False))) ∨ (((p0 → p2) → False) → False))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  apply Or.inr
  intro assump_7
  apply False.elim assump_7


variable (p6 p3 p2 p0 p4 : Prop)
theorem file36_4317 : ((((((p0 ∧ p4) ∧ (p6 ∨ False)) ∨ ((True → False) → False)) ∧ (((p6 ∧ p6) ∨ (p2 ∨ p3)) ∨ ((False ∨ False) → False))) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p0 ∧ p4) ∧ (p6 ∨ False)) ∨ ((True → False) → False)) ∧ (((p6 ∧ p6) ∨ (p2 ∨ p3)) ∨ ((False ∨ False) → False))) := by
    apply And.intro
    apply Or.inr
    intro assump_5
    have assump_23 : True := by
      apply True.intro
    let assump_8 := assump_5 assump_23
    apply False.elim assump_8
    apply Or.inr
    intro assump_12
    cases assump_12
    case inl assump_13 =>
      apply False.elim assump_13
    case inr assump_14 =>
      apply False.elim assump_14
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p4 p5 p6 p7 p3 p2 p0 p1 : Prop)
theorem file36_5099 : ((((((p2 ∨ False) → (False → p5)) ∨ ((p7 → False) → (p4 → False))) → False) ∨ ((((p1 → False) ∧ (p6 ∨ p0)) ∨ ((p1 → p2) → (p3 → False))) ∧ (((p4 ∨ p3) ∨ (p3 → False)) ∧ ((True ∧ True) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_120 : (((p2 ∨ False) → (False → p5)) ∨ ((p7 → False) → (p4 → False))) := by
      apply Or.inl
      intro assump_7
      intro assump_8
      apply False.elim assump_8
    let assump_6 := assump_2 assump_120
    apply False.elim assump_6
  case inr assump_3 =>
    cases assump_3
    case intro assump_14 assump_15 =>
      cases assump_14
      case inl assump_16 =>
        cases assump_16
        case intro assump_18 assump_19 =>
          cases assump_19
          case inl assump_22 =>
            cases assump_15
            case intro assump_26 assump_27 =>
              cases assump_26
              case inl assump_28 =>
                cases assump_28
                case inl assump_30 =>
                  have assump_121 : (True ∧ True) := by
                    apply And.intro
                    apply True.intro
                    apply True.intro
                  let assump_36 := assump_27 assump_121
                  apply False.elim assump_36
                case inr assump_31 =>
                  have assump_122 : (True ∧ True) := by
                    apply And.intro
                    apply True.intro
                    apply True.intro
                  let assump_44 := assump_27 assump_122
                  apply False.elim assump_44
              case inr assump_29 =>
                have assump_123 : (True ∧ True) := by
                  apply And.intro
                  apply True.intro
                  apply True.intro
                let assump_52 := assump_27 assump_123
                apply False.elim assump_52
          case inr assump_23 =>
            cases assump_15
            case intro assump_58 assump_59 =>
              cases assump_58
              case inl assump_60 =>
                cases assump_60
                case inl assump_62 =>
                  have assump_124 : (True ∧ True) := by
                    apply And.intro
                    apply True.intro
                    apply True.intro
                  let assump_68 := assump_59 assump_124
                  apply False.elim assump_68
                case inr assump_63 =>
                  have assump_125 : (True ∧ True) := by
                    apply And.intro
                    apply True.intro
                    apply True.intro
                  let assump_76 := assump_59 assump_125
                  apply False.elim assump_76
              case inr assump_61 =>
                have assump_126 : (True ∧ True) := by
                  apply And.intro
                  apply True.intro
                  apply True.intro
                let assump_84 := assump_59 assump_126
                apply False.elim assump_84
      case inr assump_17 =>
        cases assump_15
        case intro assump_90 assump_91 =>
          cases assump_90
          case inl assump_92 =>
            cases assump_92
            case inl assump_94 =>
              have assump_127 : (True ∧ True) := by
                apply And.intro
                apply True.intro
                apply True.intro
              let assump_100 := assump_91 assump_127
              apply False.elim assump_100
            case inr assump_95 =>
              have assump_128 : (True ∧ True) := by
                apply And.intro
                apply True.intro
                apply True.intro
              let assump_108 := assump_91 assump_128
              apply False.elim assump_108
          case inr assump_93 =>
            have assump_129 : (True ∧ True) := by
              apply And.intro
              apply True.intro
              apply True.intro
            let assump_116 := assump_91 assump_129
            apply False.elim assump_116


variable (p6 p4 p0 p1 p2 p3 p7 p5 : Prop)
theorem file36_9123 : (((((p0 ∧ False) → False) ∨ ((p2 ∧ p7) → (p4 ∨ p6))) ∧ (((p6 ∧ p4) ∧ (True → True)) ∧ ((True ∨ p3) → (p4 → False)))) → ((((p1 → False) ∧ (p5 ∨ p1)) → False) ∨ (((p7 → False) → (p2 → False)) ∨ ((p0 ∧ True) ∧ (True ∧ False))))) := by
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
            apply Or.inl
            intro assump_22
            cases assump_22
            case intro assump_23 assump_24 =>
              cases assump_24
              case inl assump_27 =>
                have assump_84 : (True ∨ p3) := by
                  apply Or.inl
                  apply True.intro
                let assump_33 := assump_9 assump_84
                have assump_85 : p4 := by
                  exact assump_13
                let assump_34 := assump_33 assump_85
                apply False.elim assump_34
              case inr assump_28 =>
                have assump_86 : p1 := by
                  exact assump_28
                let assump_41 := assump_23 assump_86
                apply False.elim assump_41
    case inr assump_5 =>
      cases assump_3
      case intro assump_47 assump_48 =>
        cases assump_47
        case intro assump_49 assump_50 =>
          cases assump_49
          case intro assump_51 assump_52 =>
            apply Or.inl
            intro assump_61
            cases assump_61
            case intro assump_62 assump_63 =>
              cases assump_63
              case inl assump_66 =>
                have assump_87 : (True ∨ p3) := by
                  apply Or.inl
                  apply True.intro
                let assump_72 := assump_48 assump_87
                have assump_88 : p4 := by
                  exact assump_52
                let assump_73 := assump_72 assump_88
                apply False.elim assump_73
              case inr assump_67 =>
                have assump_89 : p1 := by
                  exact assump_67
                let assump_80 := assump_62 assump_89
                apply False.elim assump_80


variable (p0 p5 p1 : Prop)
theorem file36_11419 : (((((p0 ∧ p1) → (True ∧ p1)) ∧ ((p5 → p1) → False)) ∧ (((True → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_23 : ((True → False) → False) := by
        intro assump_13
        have assump_24 : True := by
          apply True.intro
        let assump_16 := assump_13 assump_24
        apply False.elim assump_16
      let assump_12 := assump_3 assump_23
      apply False.elim assump_12


variable (p3 p7 p6 p2 p4 p5 p0 p1 : Prop)
theorem file36_12009 : (((((p4 → p6) ∧ (p6 → p7)) → False) → (((True → False) → (p3 → False)) ∨ ((p2 → p0) ∧ (p5 ∨ True)))) ∨ ((((p1 → False) → False) ∨ ((p5 ∨ False) → (p0 ∨ True))) → False)) := by
  apply Or.inl
  intro assump_20
  apply Or.inl
  intro assump_23
  intro assump_24
  have assump_33 : True := by
    apply True.intro
  let assump_29 := assump_23 assump_33
  apply False.elim assump_29


variable (p1 p3 p0 p7 : Prop)
theorem file36_12442 : ((((((True ∧ False) ∧ (p1 → False)) → ((True ∨ True) → False)) ∨ (((p0 ∨ p7) ∨ (p3 ∨ True)) ∧ ((p1 ∧ False) → False))) → False) → False) := by
  intro assump_1
  have assump_32 : ((((True ∧ False) ∧ (p1 → False)) → ((True ∨ True) → False)) ∨ (((p0 ∨ p7) ∨ (p3 ∨ True)) ∧ ((p1 ∧ False) → False))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_5
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          apply False.elim assump_14
    case inr assump_8 =>
      cases assump_5
      case intro assump_21 assump_22 =>
        cases assump_21
        case intro assump_23 assump_24 =>
          apply False.elim assump_24
  let assump_4 := assump_1 assump_32
  apply False.elim assump_4


variable (p2 p1 p4 p0 p7 p3 : Prop)
theorem file36_13321 : ((((((p0 → p3) → (p1 → False)) ∨ ((p2 → False) → (p4 → p7))) → (((p1 → p4) ∧ (False ∧ p7)) → ((True ∧ p4) ∨ (p3 ∧ False)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p0 → p3) → (p1 → False)) ∨ ((p2 → False) → (p4 → p7))) → (((p1 → p4) ∧ (False ∧ p7)) → ((True ∧ p4) ∨ (p3 ∧ False)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        apply False.elim assump_11
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p2 p5 p0 p1 p4 p7 p3 p6 : Prop)
theorem file36_13953 : (((((p2 → p4) ∧ (p4 → False)) → False) → False) → ((((p5 ∧ p1) ∧ (p6 → False)) ∨ ((p7 ∨ p4) ∧ (False ∨ p0))) ∨ (((p3 ∧ p4) ∧ (True ∨ p7)) → ((p2 ∨ True) ∨ (p5 → False))))) := by
  intro assump_1
  apply Or.inr
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_6
      case inl assump_13 =>
        apply Or.inl
        apply Or.inr
        apply True.intro
      case inr assump_14 =>
        apply Or.inl
        apply Or.inr
        apply True.intro


variable (p4 p2 p1 p3 p0 p7 : Prop)
theorem file36_14557 : (((((p3 ∨ p0) → (p0 ∨ p7)) ∧ ((p7 → False) → False)) → False) → ((((p3 → p4) → False) → ((p2 ∨ True) ∨ (p1 → False))) ∨ (((p0 → False) → False) ∨ ((p2 ∧ p7) → False)))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  apply Or.inl
  apply Or.inr
  apply True.intro


variable (p0 p6 p1 p4 p3 p5 : Prop)
theorem file36_14890 : (((((p0 ∨ False) → (p3 ∨ p0)) → ((p6 ∨ True) ∨ (p0 ∨ p6))) → (((p1 → False) ∨ (False ∨ p4)) → ((p3 ∨ p4) ∨ (p4 ∧ False)))) → ((((p5 → p4) ∧ (p4 ∧ False)) ∨ ((p6 → True) ∨ (p6 ∨ p0))) → (((False → False) ∧ (p4 ∧ False)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_5
    case intro assump_8 assump_9 =>
      apply False.elim assump_9


variable (p1 p3 p2 p6 p0 p7 p5 : Prop)
theorem file36_15378 : (((((p3 ∧ p5) → False) → ((p2 → False) → (p2 → False))) → False) → ((((p0 ∨ p3) → False) ∨ ((p7 ∧ False) → (p6 ∧ p6))) ∨ (((p1 ∨ False) ∧ (p6 → False)) ∨ ((True ∧ p3) ∨ (False ∨ p7))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  cases assump_4
  case inl assump_5 =>
    have assump_49 : (((p3 ∧ p5) → False) → ((p2 → False) → (p2 → False))) := by
      intro assump_11
      intro assump_12
      intro assump_13
      have assump_50 : p2 := by
        exact assump_13
      let assump_21 := assump_12 assump_50
      apply False.elim assump_21
    let assump_10 := assump_1 assump_49
    apply False.elim assump_10
  case inr assump_6 =>
    have assump_51 : (((p3 ∧ p5) → False) → ((p2 → False) → (p2 → False))) := by
      intro assump_32
      intro assump_33
      intro assump_34
      have assump_52 : p2 := by
        exact assump_34
      let assump_42 := assump_33 assump_52
      apply False.elim assump_42
    let assump_31 := assump_1 assump_51
    apply False.elim assump_31


variable (p5 p6 p2 p3 p0 : Prop)
theorem file36_16454 : (((((False ∨ True) → (p5 → p5)) ∨ ((p6 ∨ True) → False)) → False) → ((((p3 ∧ p6) ∨ (p2 → p3)) ∧ ((True ∧ p2) ∨ (p0 → False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        cases assump_4
        case inl assump_13 =>
          cases assump_13
          case intro assump_15 assump_16 =>
            have assump_99 : (((False ∨ True) → (p5 → p5)) ∨ ((p6 ∨ True) → False)) := by
              apply Or.inl
              intro assump_24
              intro assump_25
              cases assump_24
              case inl assump_28 =>
                apply False.elim assump_28
              case inr assump_29 =>
                exact assump_25
            let assump_23 := assump_1 assump_99
            apply False.elim assump_23
        case inr assump_14 =>
          have assump_100 : (((False ∨ True) → (p5 → p5)) ∨ ((p6 ∨ True) → False)) := by
            apply Or.inl
            intro assump_42
            intro assump_43
            cases assump_42
            case inl assump_46 =>
              apply False.elim assump_46
            case inr assump_47 =>
              exact assump_43
          let assump_41 := assump_1 assump_100
          apply False.elim assump_41
    case inr assump_6 =>
      cases assump_4
      case inl assump_57 =>
        cases assump_57
        case intro assump_59 assump_60 =>
          have assump_101 : (((False ∨ True) → (p5 → p5)) ∨ ((p6 ∨ True) → False)) := by
            apply Or.inl
            intro assump_68
            intro assump_69
            cases assump_68
            case inl assump_72 =>
              apply False.elim assump_72
            case inr assump_73 =>
              exact assump_69
          let assump_67 := assump_1 assump_101
          apply False.elim assump_67
      case inr assump_58 =>
        have assump_102 : (((False ∨ True) → (p5 → p5)) ∨ ((p6 ∨ True) → False)) := by
          apply Or.inl
          intro assump_86
          intro assump_87
          cases assump_86
          case inl assump_90 =>
            apply False.elim assump_90
          case inr assump_91 =>
            exact assump_87
        let assump_85 := assump_1 assump_102
        apply False.elim assump_85


variable (p3 p1 p5 p0 p2 p7 : Prop)
theorem file36_18847 : ((((((p3 → p2) ∧ (False ∧ p5)) → ((p1 ∨ False) → False)) ∨ (((p7 ∧ p7) ∧ (p0 ∧ p1)) ∨ ((p3 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_24 : ((((p3 → p2) ∧ (False ∧ p5)) → ((p1 ∨ False) → False)) ∨ (((p7 ∧ p7) ∧ (p0 ∧ p1)) ∨ ((p3 → False) → False))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_5
      case intro assump_11 assump_12 =>
        cases assump_12
        case intro assump_15 assump_16 =>
          apply False.elim assump_15
    case inr assump_8 =>
      apply False.elim assump_8
  let assump_4 := assump_1 assump_24
  apply False.elim assump_4


variable (p0 p4 p1 p3 p6 p7 p2 : Prop)
theorem file36_19581 : (((((p0 ∨ True) → False) → ((p0 → False) → (p3 → False))) → False) → ((((p0 → False) ∨ (True → p6)) ∧ ((p6 → p2) → (p0 ∧ p4))) ∧ (((p4 ∨ p7) → (p1 ∨ False)) ∨ ((False ∨ p2) → (p2 ∨ p0))))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  apply Or.inl
  intro assump_4
  have assump_113 : (((p0 ∨ True) → False) → ((p0 → False) → (p3 → False))) := by
    intro assump_9
    intro assump_10
    intro assump_11
    have assump_114 : (p0 ∨ True) := by
      apply Or.inl
      exact assump_4
    let assump_18 := assump_9 assump_114
    apply False.elim assump_18
  let assump_8 := assump_1 assump_113
  apply False.elim assump_8
  intro assump_25
  apply And.intro
  have assump_115 : (((p0 ∨ True) → False) → ((p0 → False) → (p3 → False))) := by
    intro assump_31
    intro assump_32
    intro assump_33
    have assump_116 : (p0 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_40 := assump_31 assump_116
    apply False.elim assump_40
  let assump_30 := assump_1 assump_115
  apply False.elim assump_30
  have assump_117 : (((p0 ∨ True) → False) → ((p0 → False) → (p3 → False))) := by
    intro assump_52
    intro assump_53
    intro assump_54
    have assump_118 : (p0 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_61 := assump_52 assump_118
    apply False.elim assump_61
  let assump_51 := assump_1 assump_117
  apply False.elim assump_51
  apply Or.inl
  intro assump_70
  cases assump_70
  case inl assump_71 =>
    have assump_119 : (((p0 ∨ True) → False) → ((p0 → False) → (p3 → False))) := by
      intro assump_77
      intro assump_78
      intro assump_79
      have assump_120 : (p0 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_86 := assump_77 assump_120
      apply False.elim assump_86
    let assump_76 := assump_1 assump_119
    apply False.elim assump_76
  case inr assump_72 =>
    have assump_121 : (((p0 ∨ True) → False) → ((p0 → False) → (p3 → False))) := by
      intro assump_97
      intro assump_98
      intro assump_99
      have assump_122 : (p0 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_106 := assump_97 assump_122
      apply False.elim assump_106
    let assump_96 := assump_1 assump_121
    apply False.elim assump_96


variable (p5 p0 p7 p3 p2 p4 p1 p6 : Prop)
theorem file36_21927 : (((((p5 ∧ p0) → (p5 ∨ p0)) ∧ ((p2 ∧ p1) → (p7 ∨ p2))) ∨ (((p4 ∨ p6) → (p0 ∧ p2)) → False)) ∧ ((((False → False) ∨ (p2 → False)) ∨ ((p7 → False) ∧ (False → p1))) ∨ (((p3 ∨ p0) ∧ (p5 → True)) → ((p5 → False) ∨ (p7 → p7))))) := by
  apply And.intro
  apply Or.inl
  apply And.intro
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    exact assump_2
  intro assump_8
  cases assump_8
  case intro assump_9 assump_10 =>
    apply Or.inr
    exact assump_9
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_15
  apply False.elim assump_15


variable (p7 p2 p1 p6 p3 p5 p0 p4 : Prop)
theorem file36_22573 : (((((p4 ∧ False) ∧ (p7 ∨ p4)) ∨ ((p1 → p2) → (p7 → p0))) ∨ (((p4 ∧ p6) ∧ (p3 ∧ p7)) ∨ ((p5 → p0) → False))) → ((((p6 ∧ False) → False) ∨ ((p0 → False) → False)) ∨ (((True ∧ p4) → False) → False))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          apply False.elim assump_9
    case inr assump_5 =>
      apply Or.inl
      apply Or.inl
      intro assump_16
      cases assump_16
      case intro assump_17 assump_18 =>
        apply False.elim assump_18
  case inr assump_3 =>
    cases assump_3
    case inl assump_23 =>
      cases assump_23
      case intro assump_25 assump_26 =>
        cases assump_25
        case intro assump_27 assump_28 =>
          cases assump_26
          case intro assump_33 assump_34 =>
            apply Or.inl
            apply Or.inl
            intro assump_39
            cases assump_39
            case intro assump_40 assump_41 =>
              apply False.elim assump_41
    case inr assump_24 =>
      apply Or.inl
      apply Or.inl
      intro assump_48
      cases assump_48
      case intro assump_49 assump_50 =>
        apply False.elim assump_50


variable (p4 p0 p2 p6 p3 p7 : Prop)
theorem file36_23919 : ((((((p0 ∨ p6) ∧ (True ∧ p7)) ∨ ((p4 → False) ∧ (True → False))) → (((p4 → p7) → False) → False)) → ((((True → False) ∨ (True ∨ p6)) → ((False ∨ True) ∨ (p3 ∧ p2))) → False)) → False) := by
  intro assump_1
  have assump_74 : ((((p0 ∨ p6) ∧ (True ∧ p7)) ∨ ((p4 → False) ∧ (True → False))) → (((p4 → p7) → False) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case inl assump_9 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_11
        case inl assump_13 =>
          cases assump_12
          case intro assump_17 assump_18 =>
            have assump_75 : (p4 → p7) := by
              intro assump_26
              exact assump_18
            let assump_25 := assump_6 assump_75
            apply False.elim assump_25
        case inr assump_14 =>
          cases assump_12
          case intro assump_34 assump_35 =>
            have assump_76 : (p4 → p7) := by
              intro assump_43
              exact assump_35
            let assump_42 := assump_6 assump_76
            apply False.elim assump_42
    case inr assump_10 =>
      cases assump_10
      case intro assump_49 assump_50 =>
        have assump_77 : True := by
          apply True.intro
        let assump_55 := assump_50 assump_77
        apply False.elim assump_55
  let assump_4 := assump_1 assump_74
  have assump_78 : (((True → False) ∨ (True ∨ p6)) → ((False ∨ True) ∨ (p3 ∧ p2))) := by
    intro assump_60
    cases assump_60
    case inl assump_61 =>
      apply Or.inl
      apply Or.inr
      apply True.intro
    case inr assump_62 =>
      cases assump_62
      case inl assump_65 =>
        apply Or.inl
        apply Or.inr
        apply True.intro
      case inr assump_66 =>
        apply Or.inl
        apply Or.inr
        apply True.intro
  let assump_59 := assump_4 assump_78
  apply False.elim assump_59


variable (p0 p5 p4 p2 p7 p6 : Prop)
theorem file36_25847 : (((((p4 ∧ False) → (p5 ∨ False)) → ((p7 → False) ∧ (p0 ∧ p6))) → (((p4 ∨ True) ∨ (p2 ∧ True)) ∨ ((p5 ∧ p4) → False))) ∧ ((((p0 → p2) → False) ∧ ((True ∨ p4) → False)) → False)) := by
  apply And.intro
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply Or.inr
  apply True.intro
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    have assump_15 : (True ∨ p4) := by
      apply Or.inl
      apply True.intro
    let assump_11 := assump_6 assump_15
    apply False.elim assump_11


variable (p0 p5 p1 p2 p4 p3 p7 p6 : Prop)
theorem file36_26415 : (((((p2 ∨ p2) ∨ (p0 → False)) ∧ ((p4 ∧ p4) → False)) ∧ (((False → False) ∨ (p7 ∧ p5)) ∧ ((p1 → p5) → False))) → ((((p3 → p0) ∧ (p1 ∧ False)) → ((p7 → False) → (False ∨ p6))) ∨ (((p0 → p1) ∧ (p6 ∧ p7)) ∨ ((p1 → p5) → (p2 → False))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_3
          case intro assump_14 assump_15 =>
            cases assump_14
            case inl assump_16 =>
              apply Or.inl
              intro assump_22
              intro assump_23
              cases assump_22
              case intro assump_26 assump_27 =>
                cases assump_27
                case intro assump_30 assump_31 =>
                  apply False.elim assump_31
            case inr assump_17 =>
              cases assump_17
              case intro assump_36 assump_37 =>
                apply Or.inl
                intro assump_44
                intro assump_45
                cases assump_44
                case intro assump_48 assump_49 =>
                  cases assump_49
                  case intro assump_52 assump_53 =>
                    apply False.elim assump_53
        case inr assump_9 =>
          cases assump_3
          case intro assump_62 assump_63 =>
            cases assump_62
            case inl assump_64 =>
              apply Or.inl
              intro assump_70
              intro assump_71
              cases assump_70
              case intro assump_74 assump_75 =>
                cases assump_75
                case intro assump_78 assump_79 =>
                  apply False.elim assump_79
            case inr assump_65 =>
              cases assump_65
              case intro assump_84 assump_85 =>
                apply Or.inl
                intro assump_92
                intro assump_93
                cases assump_92
                case intro assump_96 assump_97 =>
                  cases assump_97
                  case intro assump_100 assump_101 =>
                    apply False.elim assump_101
      case inr assump_7 =>
        cases assump_3
        case intro assump_110 assump_111 =>
          cases assump_110
          case inl assump_112 =>
            apply Or.inl
            intro assump_118
            intro assump_119
            cases assump_118
            case intro assump_122 assump_123 =>
              cases assump_123
              case intro assump_126 assump_127 =>
                apply False.elim assump_127
          case inr assump_113 =>
            cases assump_113
            case intro assump_132 assump_133 =>
              apply Or.inl
              intro assump_140
              intro assump_141
              cases assump_140
              case intro assump_144 assump_145 =>
                cases assump_145
                case intro assump_148 assump_149 =>
                  apply False.elim assump_149


variable (p4 p3 p0 p7 p1 p5 p6 : Prop)
theorem file36_29508 : ((((((p0 → False) ∨ (p6 → p7)) ∧ ((p1 ∧ p7) ∧ (p4 → False))) ∨ (((p5 ∧ p4) ∨ (p3 ∨ p5)) ∧ ((False → p6) ∧ (p6 → p1)))) ∧ ((((p5 ∨ p0) ∨ (p5 → p4)) ∨ ((p4 → False) ∨ (p1 → p6))) → False)) → False) := by
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
            cases assump_12
            case intro assump_14 assump_15 =>
              have assump_122 : (((p5 ∨ p0) ∨ (p5 → p4)) ∨ ((p4 → False) ∨ (p1 → p6))) := by
                apply Or.inl
                apply Or.inr
                intro assump_25
                have assump_123 : (((p5 ∨ p0) ∨ (p5 → p4)) ∨ ((p4 → False) ∨ (p1 → p6))) := by
                  apply Or.inl
                  apply Or.inl
                  apply Or.inl
                  exact assump_25
                let assump_29 := assump_3 assump_123
                apply False.elim assump_29
              let assump_24 := assump_3 assump_122
              apply False.elim assump_24
        case inr assump_9 =>
          cases assump_7
          case intro assump_38 assump_39 =>
            cases assump_38
            case intro assump_40 assump_41 =>
              have assump_124 : (((p5 ∨ p0) ∨ (p5 → p4)) ∨ ((p4 → False) ∨ (p1 → p6))) := by
                apply Or.inl
                apply Or.inr
                intro assump_51
                have assump_125 : (((p5 ∨ p0) ∨ (p5 → p4)) ∨ ((p4 → False) ∨ (p1 → p6))) := by
                  apply Or.inl
                  apply Or.inl
                  apply Or.inl
                  exact assump_51
                let assump_55 := assump_3 assump_125
                apply False.elim assump_55
              let assump_50 := assump_3 assump_124
              apply False.elim assump_50
    case inr assump_5 =>
      cases assump_5
      case intro assump_62 assump_63 =>
        cases assump_62
        case inl assump_64 =>
          cases assump_64
          case intro assump_66 assump_67 =>
            cases assump_63
            case intro assump_72 assump_73 =>
              have assump_126 : (((p5 ∨ p0) ∨ (p5 → p4)) ∨ ((p4 → False) ∨ (p1 → p6))) := by
                apply Or.inl
                apply Or.inl
                apply Or.inl
                exact assump_66
              let assump_80 := assump_3 assump_126
              apply False.elim assump_80
        case inr assump_65 =>
          cases assump_65
          case inl assump_84 =>
            cases assump_63
            case intro assump_88 assump_89 =>
              have assump_127 : (((p5 ∨ p0) ∨ (p5 → p4)) ∨ ((p4 → False) ∨ (p1 → p6))) := by
                apply Or.inl
                apply Or.inr
                intro assump_97
                have assump_128 : (((p5 ∨ p0) ∨ (p5 → p4)) ∨ ((p4 → False) ∨ (p1 → p6))) := by
                  apply Or.inl
                  apply Or.inl
                  apply Or.inl
                  exact assump_97
                let assump_101 := assump_3 assump_128
                apply False.elim assump_101
              let assump_96 := assump_3 assump_127
              apply False.elim assump_96
          case inr assump_85 =>
            cases assump_63
            case intro assump_110 assump_111 =>
              have assump_129 : (((p5 ∨ p0) ∨ (p5 → p4)) ∨ ((p4 → False) ∨ (p1 → p6))) := by
                apply Or.inl
                apply Or.inl
                apply Or.inl
                exact assump_85
              let assump_118 := assump_3 assump_129
              apply False.elim assump_118


variable (p0 p1 p4 : Prop)
theorem file36_33244 : (((((p1 ∧ p0) → False) → ((p0 ∨ p4) → (True ∨ True))) → False) → False) := by
  intro assump_1
  have assump_20 : (((p1 ∧ p0) → False) → ((p0 ∨ p4) → (True ∨ True))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      apply Or.inl
      apply True.intro
    case inr assump_8 =>
      apply Or.inl
      apply True.intro
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p4 p2 p1 p5 : Prop)
theorem file36_33726 : ((((((p4 → False) → False) → ((p1 → False) → (p5 → p5))) ∨ (((p1 → True) → False) ∧ ((False → p2) → (p5 → False)))) → False) → False) := by
  intro assump_1
  have assump_17 : ((((p4 → False) → False) → ((p1 → False) → (p5 → p5))) ∨ (((p1 → True) → False) ∧ ((False → p2) → (p5 → False)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    exact assump_7
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p7 p0 p2 p4 : Prop)
theorem file36_34234 : ((((((True ∧ False) ∨ (p2 ∧ p2)) → ((p2 → False) → (p4 → False))) → (((p0 → p4) ∧ (False ∧ p7)) → False)) → False) → False) := by
  intro assump_1
  have assump_18 : ((((True ∧ False) ∨ (p2 ∧ p2)) → ((p2 → False) → (p4 → False))) → (((p0 → p4) ∧ (False ∧ p7)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        apply False.elim assump_11
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p3 p6 p2 p0 : Prop)
theorem file36_34818 : ((((((p0 ∧ p3) ∧ (p0 ∧ p6)) ∧ ((False → p2) ∧ (p3 → False))) → False) → False) → False) := by
  intro assump_5
  have assump_39 : ((((p0 ∧ p3) ∧ (p0 ∧ p6)) ∧ ((False → p2) ∧ (p3 → False))) → False) := by
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_12
        case intro assump_14 assump_15 =>
          cases assump_13
          case intro assump_20 assump_21 =>
            cases assump_11
            case intro assump_26 assump_27 =>
              have assump_40 : p3 := by
                exact assump_15
              let assump_32 := assump_27 assump_40
              apply False.elim assump_32
  let assump_8 := assump_5 assump_39
  apply False.elim assump_8


variable (p7 p5 p1 p6 p3 p2 p0 p4 : Prop)
theorem file36_35665 : (((((p3 → p6) ∧ (p6 → p1)) → False) → (((p4 ∧ False) ∧ (p5 ∨ p5)) → False)) ∨ ((((p4 ∨ p7) → (p0 ∧ p1)) ∨ ((p5 ∧ p5) ∨ (p2 → p1))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      apply False.elim assump_6


variable (p5 p1 p7 p0 p4 p2 p6 p3 : Prop)
theorem file36_36065 : ((((((p4 → p1) ∨ (p7 → p4)) ∧ ((p3 → p2) → False)) ∧ (((p7 ∨ p6) ∧ (p5 → False)) ∧ ((p0 ∨ p3) ∧ (False ∧ p7)))) ∧ ((((p6 ∧ p2) → False) ∧ ((p6 ∨ p4) ∧ (p2 ∨ False))) → (((p0 ∨ p3) → (p7 → p4)) → ((True → p2) ∧ (p6 → p7))))) → False) := by
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
          case intro assump_14 assump_15 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              cases assump_16
              case inl assump_18 =>
                cases assump_15
                case intro assump_24 assump_25 =>
                  cases assump_24
                  case inl assump_26 =>
                    cases assump_25
                    case intro assump_30 assump_31 =>
                      apply False.elim assump_30
                  case inr assump_27 =>
                    cases assump_25
                    case intro assump_36 assump_37 =>
                      apply False.elim assump_36
              case inr assump_19 =>
                cases assump_15
                case intro assump_44 assump_45 =>
                  cases assump_44
                  case inl assump_46 =>
                    cases assump_45
                    case intro assump_50 assump_51 =>
                      apply False.elim assump_50
                  case inr assump_47 =>
                    cases assump_45
                    case intro assump_56 assump_57 =>
                      apply False.elim assump_56
        case inr assump_9 =>
          cases assump_5
          case intro assump_64 assump_65 =>
            cases assump_64
            case intro assump_66 assump_67 =>
              cases assump_66
              case inl assump_68 =>
                cases assump_65
                case intro assump_74 assump_75 =>
                  cases assump_74
                  case inl assump_76 =>
                    cases assump_75
                    case intro assump_80 assump_81 =>
                      apply False.elim assump_80
                  case inr assump_77 =>
                    cases assump_75
                    case intro assump_86 assump_87 =>
                      apply False.elim assump_86
              case inr assump_69 =>
                cases assump_65
                case intro assump_94 assump_95 =>
                  cases assump_94
                  case inl assump_96 =>
                    cases assump_95
                    case intro assump_100 assump_101 =>
                      apply False.elim assump_100
                  case inr assump_97 =>
                    cases assump_95
                    case intro assump_106 assump_107 =>
                      apply False.elim assump_106


variable (p2 p0 p6 : Prop)
theorem file36_39010 : (((((p6 ∨ p2) → (True ∧ True)) → False) → False) ∨ ((((p6 → p6) ∨ (True ∨ True)) → ((p0 → p0) → False)) → False)) := by
  apply Or.inl
  intro assump_14
  have assump_22 : ((p6 ∨ p2) → (True ∧ True)) := by
    intro assump_18
    apply And.intro
    apply True.intro
    apply True.intro
  let assump_17 := assump_14 assump_22
  apply False.elim assump_17


variable (p5 p6 p4 : Prop)
theorem file36_39417 : ((((((p5 → False) → (p4 ∧ False)) ∧ ((False ∧ p5) ∧ (p6 → False))) → False) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p5 → False) → (p4 ∧ False)) ∧ ((False ∧ p5) ∧ (p6 → False))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          apply False.elim assump_12
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p5 p0 p7 p1 p6 p2 p4 : Prop)
theorem file36_39999 : (((((False ∧ p7) ∧ (p6 → p7)) ∧ ((p2 ∨ p2) → False)) → False) ∨ ((((p6 → p2) ∨ (p5 ∨ p1)) ∧ ((p4 → False) → False)) ∨ (((p5 ∧ p0) → (p6 ∧ False)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        apply False.elim assump_6


variable (p1 p6 p5 p0 p3 p2 : Prop)
theorem file36_40453 : ((((((p3 ∧ p6) → (p1 ∧ p3)) → False) → (((p0 → p6) → (p5 → p6)) → ((p1 ∨ p0) → (p2 ∨ p0)))) → False) → False) := by
  intro assump_1
  have assump_42 : ((((p3 ∧ p6) → (p1 ∧ p3)) → False) → (((p0 → p6) → (p5 → p6)) → ((p1 ∨ p0) → (p2 ∨ p0)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_7
    case inl assump_8 =>
      have assump_43 : ((p3 ∧ p6) → (p1 ∧ p3)) := by
        intro assump_17
        apply And.intro
        cases assump_17
        case intro assump_18 assump_19 =>
          exact assump_8
        cases assump_17
        case intro assump_24 assump_25 =>
          exact assump_24
      let assump_16 := assump_5 assump_43
      apply False.elim assump_16
    case inr assump_9 =>
      apply Or.inr
      exact assump_9
  let assump_4 := assump_1 assump_42
  apply False.elim assump_4


variable (p3 p4 p0 p2 p1 p5 p6 p7 : Prop)
theorem file36_41357 : ((((((p0 ∧ p3) ∧ (p1 ∨ True)) ∧ ((p7 ∧ p6) → False)) ∨ (((p2 → False) ∧ (False ∨ p3)) ∨ ((p5 ∧ False) ∨ (p6 → p6)))) ∧ ((((p4 → True) ∨ (p3 → False)) ∧ ((p3 ∧ p4) → (False → p5))) → (((p1 → True) → False) ∧ ((p0 → False) ∧ (p2 ∧ p6))))) → False) := by
  intro assump_39
  cases assump_39
  case intro assump_40 assump_41 =>
    cases assump_40
    case inl assump_42 =>
      cases assump_42
      case intro assump_44 assump_45 =>
        cases assump_44
        case intro assump_46 assump_47 =>
          cases assump_46
          case intro assump_48 assump_49 =>
            cases assump_47
            case inl assump_54 =>
              have assump_142 : (((p4 → True) ∨ (p3 → False)) ∧ ((p3 ∧ p4) → (False → p5))) := by
                apply And.intro
                apply Or.inl
                intro assump_63
                apply True.intro
                intro assump_64
                intro assump_65
                apply False.elim assump_65
              let assump_62 := assump_41 assump_142
              let assump_68 := And.left assump_62
              have assump_143 : (p1 → True) := by
                intro assump_70
                apply True.intro
              let assump_69 := assump_68 assump_143
              apply False.elim assump_69
            case inr assump_55 =>
              have assump_144 : (((p4 → True) ∨ (p3 → False)) ∧ ((p3 ∧ p4) → (False → p5))) := by
                apply And.intro
                apply Or.inl
                intro assump_81
                apply True.intro
                intro assump_82
                intro assump_83
                apply False.elim assump_83
              let assump_80 := assump_41 assump_144
              let assump_86 := And.left assump_80
              have assump_145 : (p1 → True) := by
                intro assump_88
                apply True.intro
              let assump_87 := assump_86 assump_145
              apply False.elim assump_87
    case inr assump_43 =>
      cases assump_43
      case inl assump_92 =>
        cases assump_92
        case intro assump_94 assump_95 =>
          cases assump_95
          case inl assump_98 =>
            apply False.elim assump_98
          case inr assump_99 =>
            have assump_146 : (((p4 → True) ∨ (p3 → False)) ∧ ((p3 ∧ p4) → (False → p5))) := by
              apply And.intro
              apply Or.inl
              intro assump_107
              apply True.intro
              intro assump_108
              intro assump_109
              apply False.elim assump_109
            let assump_106 := assump_41 assump_146
            let assump_112 := And.left assump_106
            have assump_147 : (p1 → True) := by
              intro assump_114
              apply True.intro
            let assump_113 := assump_112 assump_147
            apply False.elim assump_113
      case inr assump_93 =>
        cases assump_93
        case inl assump_118 =>
          cases assump_118
          case intro assump_120 assump_121 =>
            apply False.elim assump_121
        case inr assump_119 =>
          have assump_148 : (((p4 → True) ∨ (p3 → False)) ∧ ((p3 ∧ p4) → (False → p5))) := by
            apply And.intro
            apply Or.inl
            intro assump_131
            apply True.intro
            intro assump_132
            intro assump_133
            apply False.elim assump_133
          let assump_130 := assump_41 assump_148
          let assump_136 := And.left assump_130
          have assump_149 : (p1 → True) := by
            intro assump_138
            apply True.intro
          let assump_137 := assump_136 assump_149
          apply False.elim assump_137


variable (p3 p6 p7 p5 p1 : Prop)
theorem file36_45072 : (((((False → False) → False) → False) → False) → ((((True ∨ p6) ∨ (p1 ∨ p6)) ∧ ((p6 → False) → (p6 → False))) ∨ (((p5 → True) → (p1 ∧ True)) → ((p3 ∧ p6) → (True ∧ p7))))) := by
  intro assump_1
  apply Or.inl
  apply And.intro
  apply Or.inl
  apply Or.inl
  apply True.intro
  intro assump_4
  intro assump_5
  have assump_14 : p6 := by
    exact assump_5
  let assump_10 := assump_4 assump_14
  apply False.elim assump_10


variable (p3 p4 p5 p2 p1 p7 p0 : Prop)
theorem file36_45560 : ((((((p3 → False) ∨ (p2 ∨ True)) ∧ ((p3 ∨ p0) ∧ (p5 → False))) ∧ (((p5 ∧ p3) ∧ (p4 → p1)) ∧ ((False → p7) → (p1 ∧ p1)))) ∧ ((((p5 → False) → False) ∨ ((p2 → False) ∨ (p4 ∨ p1))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_7
          case intro assump_12 assump_13 =>
            cases assump_12
            case inl assump_14 =>
              cases assump_5
              case intro assump_20 assump_21 =>
                cases assump_20
                case intro assump_22 assump_23 =>
                  cases assump_22
                  case intro assump_24 assump_25 =>
                    have assump_216 : (((p5 → False) → False) ∨ ((p2 → False) ∨ (p4 ∨ p1))) := by
                      apply Or.inl
                      intro assump_37
                      have assump_217 : p5 := by
                        exact assump_24
                      let assump_40 := assump_37 assump_217
                      apply False.elim assump_40
                    let assump_36 := assump_3 assump_216
                    apply False.elim assump_36
            case inr assump_15 =>
              cases assump_5
              case intro assump_51 assump_52 =>
                cases assump_51
                case intro assump_53 assump_54 =>
                  cases assump_53
                  case intro assump_55 assump_56 =>
                    have assump_218 : (((p5 → False) → False) ∨ ((p2 → False) ∨ (p4 ∨ p1))) := by
                      apply Or.inl
                      intro assump_68
                      have assump_219 : p5 := by
                        exact assump_55
                      let assump_71 := assump_68 assump_219
                      apply False.elim assump_71
                    let assump_67 := assump_3 assump_218
                    apply False.elim assump_67
        case inr assump_9 =>
          cases assump_9
          case inl assump_78 =>
            cases assump_7
            case intro assump_82 assump_83 =>
              cases assump_82
              case inl assump_84 =>
                cases assump_5
                case intro assump_90 assump_91 =>
                  cases assump_90
                  case intro assump_92 assump_93 =>
                    cases assump_92
                    case intro assump_94 assump_95 =>
                      have assump_220 : (((p5 → False) → False) ∨ ((p2 → False) ∨ (p4 ∨ p1))) := by
                        apply Or.inl
                        intro assump_107
                        have assump_221 : p5 := by
                          exact assump_94
                        let assump_110 := assump_107 assump_221
                        apply False.elim assump_110
                      let assump_106 := assump_3 assump_220
                      apply False.elim assump_106
              case inr assump_85 =>
                cases assump_5
                case intro assump_121 assump_122 =>
                  cases assump_121
                  case intro assump_123 assump_124 =>
                    cases assump_123
                    case intro assump_125 assump_126 =>
                      have assump_222 : (((p5 → False) → False) ∨ ((p2 → False) ∨ (p4 ∨ p1))) := by
                        apply Or.inl
                        intro assump_138
                        have assump_223 : p5 := by
                          exact assump_125
                        let assump_141 := assump_138 assump_223
                        apply False.elim assump_141
                      let assump_137 := assump_3 assump_222
                      apply False.elim assump_137
          case inr assump_79 =>
            cases assump_7
            case intro assump_150 assump_151 =>
              cases assump_150
              case inl assump_152 =>
                cases assump_5
                case intro assump_158 assump_159 =>
                  cases assump_158
                  case intro assump_160 assump_161 =>
                    cases assump_160
                    case intro assump_162 assump_163 =>
                      have assump_224 : (((p5 → False) → False) ∨ ((p2 → False) ∨ (p4 ∨ p1))) := by
                        apply Or.inl
                        intro assump_175
                        have assump_225 : p5 := by
                          exact assump_162
                        let assump_178 := assump_175 assump_225
                        apply False.elim assump_178
                      let assump_174 := assump_3 assump_224
                      apply False.elim assump_174
              case inr assump_153 =>
                cases assump_5
                case intro assump_189 assump_190 =>
                  cases assump_189
                  case intro assump_191 assump_192 =>
                    cases assump_191
                    case intro assump_193 assump_194 =>
                      have assump_226 : (((p5 → False) → False) ∨ ((p2 → False) ∨ (p4 ∨ p1))) := by
                        apply Or.inl
                        intro assump_206
                        have assump_227 : p5 := by
                          exact assump_193
                        let assump_209 := assump_206 assump_227
                        apply False.elim assump_209
                      let assump_205 := assump_3 assump_226
                      apply False.elim assump_205


variable (p4 p0 p5 p1 p7 p3 p2 : Prop)
theorem file36_51177 : (((((False ∨ p2) ∨ (p5 → p2)) ∨ ((p2 ∨ p1) → False)) ∧ (((p2 ∧ p0) ∧ (False → p0)) → False)) → ((((p3 ∨ p3) → False) ∧ ((p4 → True) ∧ (p3 ∧ p7))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        cases assump_1
        case intro assump_17 assump_18 =>
          cases assump_17
          case inl assump_19 =>
            cases assump_19
            case inl assump_21 =>
              cases assump_21
              case inl assump_23 =>
                apply False.elim assump_23
              case inr assump_24 =>
                have assump_66 : (p3 ∨ p3) := by
                  apply Or.inl
                  exact assump_11
                let assump_36 := assump_3 assump_66
                apply False.elim assump_36
            case inr assump_22 =>
              have assump_67 : (p3 ∨ p3) := by
                apply Or.inl
                exact assump_11
              let assump_49 := assump_3 assump_67
              apply False.elim assump_49
          case inr assump_20 =>
            have assump_68 : (p3 ∨ p3) := by
              apply Or.inl
              exact assump_11
            let assump_62 := assump_3 assump_68
            apply False.elim assump_62


variable (p6 p5 p2 p7 p0 p3 : Prop)
theorem file36_52593 : ((((((p3 ∨ False) → (p2 ∧ p0)) ∧ ((True ∨ p7) ∧ (p0 ∧ p6))) → (((False → False) ∧ (p5 ∧ False)) → ((True → False) → False))) → False) → False) := by
  intro assump_15
  have assump_37 : ((((p3 ∨ False) → (p2 ∧ p0)) ∧ ((True ∨ p7) ∧ (p0 ∧ p6))) → (((False → False) ∧ (p5 ∧ False)) → ((True → False) → False))) := by
    intro assump_19
    intro assump_20
    intro assump_21
    cases assump_20
    case intro assump_24 assump_25 =>
      cases assump_25
      case intro assump_28 assump_29 =>
        apply False.elim assump_29
  let assump_18 := assump_15 assump_37
  apply False.elim assump_18


variable (p7 p0 p1 p5 : Prop)
theorem file36_53245 : ((((((p0 ∨ False) ∧ (p7 ∧ p7)) → ((True ∨ p5) ∨ (p1 ∨ p7))) ∨ (((p0 → False) ∧ (p7 ∧ False)) ∨ ((p0 ∨ False) → False))) → False) → False) := by
  intro assump_1
  have assump_23 : ((((p0 ∨ False) ∧ (p7 ∧ p7)) → ((True ∨ p5) ∨ (p1 ∨ p7))) ∨ (((p0 → False) ∧ (p7 ∧ False)) ∨ ((p0 ∨ False) → False))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case intro assump_12 assump_13 =>
          apply Or.inl
          apply Or.inl
          apply True.intro
      case inr assump_9 =>
        apply False.elim assump_9
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p5 p1 p2 p6 p3 p0 p7 : Prop)
theorem file36_54015 : ((((((p2 ∧ True) → (p1 ∨ p6)) ∧ ((False → p7) ∨ (p0 → True))) ∧ (((p3 → False) → (True → False)) ∨ ((p0 ∨ False) → False))) ∧ ((((True ∧ p7) ∨ (p1 → p1)) ∨ ((True ∧ p5) → (p2 → p5))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case inl assump_10 =>
          cases assump_5
          case inl assump_14 =>
            have assump_64 : (((True ∧ p7) ∨ (p1 → p1)) ∨ ((True ∧ p5) → (p2 → p5))) := by
              apply Or.inl
              apply Or.inr
              intro assump_21
              exact assump_21
            let assump_20 := assump_3 assump_64
            apply False.elim assump_20
          case inr assump_15 =>
            have assump_65 : (((True ∧ p7) ∨ (p1 → p1)) ∨ ((True ∧ p5) → (p2 → p5))) := by
              apply Or.inl
              apply Or.inr
              intro assump_32
              exact assump_32
            let assump_31 := assump_3 assump_65
            apply False.elim assump_31
        case inr assump_11 =>
          cases assump_5
          case inl assump_40 =>
            have assump_66 : (((True ∧ p7) ∨ (p1 → p1)) ∨ ((True ∧ p5) → (p2 → p5))) := by
              apply Or.inl
              apply Or.inr
              intro assump_47
              exact assump_47
            let assump_46 := assump_3 assump_66
            apply False.elim assump_46
          case inr assump_41 =>
            have assump_67 : (((True ∧ p7) ∨ (p1 → p1)) ∨ ((True ∧ p5) → (p2 → p5))) := by
              apply Or.inl
              apply Or.inr
              intro assump_58
              exact assump_58
            let assump_57 := assump_3 assump_67
            apply False.elim assump_57


variable (p2 p4 p1 p6 p0 p5 p7 : Prop)
theorem file36_55897 : (((((p2 ∨ p6) → (False → False)) → False) ∧ (((p1 → p4) ∧ (False → p0)) → False)) → ((((True → False) ∧ (p2 ∨ p0)) → False) ∨ (((p2 → False) ∧ (False ∧ p5)) ∨ ((p7 → p0) → False)))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      cases assump_10
      case inl assump_13 =>
        have assump_29 : True := by
          apply True.intro
        let assump_18 := assump_9 assump_29
        apply False.elim assump_18
      case inr assump_14 =>
        have assump_30 : True := by
          apply True.intro
        let assump_25 := assump_9 assump_30
        apply False.elim assump_25


variable (p4 p3 p6 p0 p7 p5 : Prop)
theorem file36_56667 : (((((p5 ∨ p7) → False) ∧ ((p3 → False) ∧ (p3 ∧ p0))) ∧ (((p4 ∨ False) → False) ∨ ((True → False) ∧ (False ∨ False)))) → ((((p0 → p6) ∨ (p0 → p0)) ∧ ((p3 ∨ p0) → False)) → (((True → False) → False) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_6
    case inl assump_8 =>
      cases assump_1
      case intro assump_14 assump_15 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          cases assump_17
          case intro assump_20 assump_21 =>
            cases assump_21
            case intro assump_24 assump_25 =>
              cases assump_15
              case inl assump_30 =>
                have assump_92 : p3 := by
                  exact assump_24
                let assump_37 := assump_20 assump_92
                apply False.elim assump_37
              case inr assump_31 =>
                cases assump_31
                case intro assump_41 assump_42 =>
                  cases assump_42
                  case inl assump_45 =>
                    apply False.elim assump_45
                  case inr assump_46 =>
                    apply False.elim assump_46
    case inr assump_9 =>
      cases assump_1
      case intro assump_55 assump_56 =>
        cases assump_55
        case intro assump_57 assump_58 =>
          cases assump_58
          case intro assump_61 assump_62 =>
            cases assump_62
            case intro assump_65 assump_66 =>
              cases assump_56
              case inl assump_71 =>
                have assump_93 : p3 := by
                  exact assump_65
                let assump_78 := assump_61 assump_93
                apply False.elim assump_78
              case inr assump_72 =>
                cases assump_72
                case intro assump_82 assump_83 =>
                  cases assump_83
                  case inl assump_86 =>
                    apply False.elim assump_86
                  case inr assump_87 =>
                    apply False.elim assump_87


variable (p0 p2 p5 p1 p7 p3 : Prop)
theorem file36_58782 : (((((p5 → p1) → False) ∧ ((True ∧ p7) → False)) → (((p0 → p2) ∧ (p1 ∧ p3)) → False)) ∨ ((((p1 ∨ False) ∨ (p2 ∧ p7)) → ((p3 → True) ∨ (p3 → p0))) ∧ (((p2 → p2) ∨ (p1 ∨ p7)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      cases assump_1
      case intro assump_13 assump_14 =>
        have assump_27 : (p5 → p1) := by
          intro assump_21
          exact assump_7
        let assump_20 := assump_13 assump_27
        apply False.elim assump_20


variable (p3 p2 p0 p1 p4 : Prop)
theorem file36_59416 : (((((p3 ∨ p0) → (p0 ∨ p2)) → ((p2 ∨ p1) ∨ (p4 ∨ True))) ∨ (((False → False) → False) → False)) ∨ ((((p1 → p3) → (p0 → False)) → False) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inr
  apply Or.inr
  apply True.intro


variable (p3 p7 p4 p0 p1 p6 p5 : Prop)
theorem file36_59726 : (((((True ∧ p0) ∧ (p6 → p5)) ∧ ((p5 → False) → False)) ∨ (((p7 ∧ p0) → (p4 ∧ p5)) ∧ ((p5 ∨ p3) → (p6 ∨ p3)))) → ((((False → False) ∨ (p6 ∧ p3)) → False) → (((p3 ∨ p0) ∨ (p6 ∨ p1)) ∧ ((False → p0) ∨ (p4 ∧ True))))) := by
  intro assump_10
  intro assump_11
  apply And.intro
  cases assump_10
  case inl assump_14 =>
    cases assump_14
    case intro assump_16 assump_17 =>
      cases assump_16
      case intro assump_18 assump_19 =>
        cases assump_18
        case intro assump_20 assump_21 =>
          apply Or.inl
          apply Or.inr
          exact assump_21
  case inr assump_15 =>
    cases assump_15
    case intro assump_30 assump_31 =>
      have assump_75 : ((False → False) ∨ (p6 ∧ p3)) := by
        apply Or.inl
        intro assump_39
        apply False.elim assump_39
      let assump_38 := assump_11 assump_75
      apply False.elim assump_38
  cases assump_10
  case inl assump_47 =>
    cases assump_47
    case intro assump_49 assump_50 =>
      cases assump_49
      case intro assump_51 assump_52 =>
        cases assump_51
        case intro assump_53 assump_54 =>
          apply Or.inl
          intro assump_63
          apply False.elim assump_63
  case inr assump_48 =>
    cases assump_48
    case intro assump_66 assump_67 =>
      apply Or.inl
      intro assump_72
      apply False.elim assump_72


variable (p6 p4 p0 p3 p2 p5 : Prop)
theorem file36_61127 : (((((True ∧ False) ∧ (p4 ∧ False)) ∧ ((p5 ∧ p3) → (p2 → False))) ∧ (((p6 ∨ p5) → (p0 ∨ True)) ∨ ((p0 → p3) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          apply False.elim assump_9


variable (p3 p1 p5 p7 p2 p6 p4 p0 : Prop)
theorem file36_61607 : (((((False → p4) → (p5 → p3)) ∧ ((p1 ∧ p0) → False)) ∨ (((True → p5) ∨ (p2 → False)) ∧ ((True → False) ∧ (p3 → False)))) → ((((p6 ∧ p5) ∧ (p2 ∨ p1)) ∨ ((p3 → p1) → (False → False))) ∨ (((False ∧ p1) → False) ∨ ((p0 → False) → (p7 ∧ p5))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply Or.inl
      apply Or.inr
      intro assump_10
      intro assump_11
      apply False.elim assump_11
  case inr assump_3 =>
    cases assump_3
    case intro assump_14 assump_15 =>
      cases assump_14
      case inl assump_16 =>
        cases assump_15
        case intro assump_20 assump_21 =>
          apply Or.inl
          apply Or.inr
          intro assump_26
          intro assump_27
          apply False.elim assump_27
      case inr assump_17 =>
        cases assump_15
        case intro assump_32 assump_33 =>
          apply Or.inl
          apply Or.inr
          intro assump_38
          intro assump_39
          apply False.elim assump_39


variable (p1 p2 p3 p0 p4 : Prop)
theorem file36_62697 : ((((((p0 → False) ∧ (p4 ∧ True)) → False) ∨ (((True ∧ True) ∨ (p3 ∨ False)) → ((p1 → False) ∨ (p0 ∧ p1)))) ∧ ((((p2 ∨ p1) → (p4 ∨ True)) → ((True → False) → False)) → False)) → False) := by
  intro assump_21
  cases assump_21
  case intro assump_22 assump_23 =>
    cases assump_22
    case inl assump_24 =>
      have assump_64 : (((p2 ∨ p1) → (p4 ∨ True)) → ((True → False) → False)) := by
        intro assump_31
        intro assump_32
        have assump_65 : True := by
          apply True.intro
        let assump_38 := assump_32 assump_65
        apply False.elim assump_38
      let assump_30 := assump_23 assump_64
      apply False.elim assump_30
    case inr assump_25 =>
      have assump_66 : (((p2 ∨ p1) → (p4 ∨ True)) → ((True → False) → False)) := by
        intro assump_50
        intro assump_51
        have assump_67 : True := by
          apply True.intro
        let assump_57 := assump_51 assump_67
        apply False.elim assump_57
      let assump_49 := assump_23 assump_66
      apply False.elim assump_49


variable (p1 p5 p2 p7 p0 p4 : Prop)
theorem file36_63793 : ((((((True → p5) → False) ∧ ((False → p4) → (p4 → p2))) → False) ∧ ((((p2 → p0) ∧ (p1 → False)) → ((p5 → False) → (p7 → p7))) → False)) → False) := by
  intro assump_12
  cases assump_12
  case intro assump_13 assump_14 =>
    have assump_36 : (((p2 → p0) ∧ (p1 → False)) → ((p5 → False) → (p7 → p7))) := by
      intro assump_20
      intro assump_21
      intro assump_22
      cases assump_20
      case intro assump_27 assump_28 =>
        exact assump_22
    let assump_19 := assump_14 assump_36
    apply False.elim assump_19


variable (p1 p7 p2 p0 p3 p6 : Prop)
theorem file36_64385 : (((((p7 → p7) → False) → False) ∨ (((p6 ∧ p3) → (p6 ∧ p6)) ∨ ((p3 → False) ∨ (p7 → False)))) ∨ ((((p6 ∧ p0) ∧ (False → False)) ∧ ((p1 → p7) ∧ (p6 ∨ p2))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_22
  have assump_32 : (p7 → p7) := by
    intro assump_26
    exact assump_26
  let assump_25 := assump_22 assump_32
  apply False.elim assump_25


variable (p0 p7 p1 p4 : Prop)
theorem file36_64800 : ((((((False → p1) → False) → ((p0 → False) ∧ (p0 ∧ p4))) → False) ∧ ((((False → False) ∨ (True ∨ p7)) ∨ ((p0 → True) ∧ (p0 → p0))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : (((False → False) ∨ (True ∨ p7)) ∨ ((p0 → True) ∧ (p0 → p0))) := by
      apply Or.inl
      apply Or.inl
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p4 p1 p6 p7 p2 p5 : Prop)
theorem file36_65333 : ((((((p4 ∧ p2) → False) ∧ ((p1 ∨ p7) → False)) ∧ (((p7 → p5) → False) ∧ ((p1 → False) → (p5 ∧ p1)))) ∧ ((((False → False) ∨ (p1 ∧ p6)) ∨ ((p2 → p4) → (p7 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_5
        case intro assump_12 assump_13 =>
          have assump_27 : (((False → False) ∨ (p1 ∧ p6)) ∨ ((p2 → p4) → (p7 → False))) := by
            apply Or.inl
            apply Or.inl
            intro assump_21
            apply False.elim assump_21
          let assump_20 := assump_3 assump_27
          apply False.elim assump_20


variable (p4 p5 p3 p0 p6 p1 p7 : Prop)
theorem file36_66127 : (((((True ∧ p0) ∨ (p3 → False)) → False) → (((p3 → True) → (p6 → False)) → ((p0 → False) ∨ (p7 → p7)))) ∨ ((((p4 → False) ∨ (p1 → False)) ∨ ((p5 ∧ p0) ∧ (p5 → p1))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  have assump_15 : ((True ∧ p0) ∨ (p3 → False)) := by
    apply Or.inl
    apply And.intro
    apply True.intro
    exact assump_7
  let assump_11 := assump_1 assump_15
  apply False.elim assump_11


variable (p2 p6 p0 p5 p3 p4 : Prop)
theorem file36_66647 : ((((((False → p2) ∧ (p3 ∧ p6)) → ((p2 → p2) → (p6 ∨ p0))) → (((p2 → False) ∧ (p2 ∧ p3)) ∨ ((p2 ∧ p6) ∧ (p6 → False)))) ∧ ((((False ∧ p3) → False) ∨ ((p6 ∧ p4) ∨ (True → p5))) ∧ (((False → False) ∧ (True → False)) ∨ ((False → False) ∧ (True ∧ p0))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case inl assump_12 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            have assump_243 : True := by
              apply True.intro
            let assump_20 := assump_15 assump_243
            apply False.elim assump_20
        case inr assump_13 =>
          cases assump_13
          case intro assump_24 assump_25 =>
            cases assump_25
            case intro assump_28 assump_29 =>
              have assump_244 : (((False → p2) ∧ (p3 ∧ p6)) → ((p2 → p2) → (p6 ∨ p0))) := by
                intro assump_38
                intro assump_39
                cases assump_38
                case intro assump_42 assump_43 =>
                  cases assump_43
                  case intro assump_46 assump_47 =>
                    apply Or.inl
                    exact assump_47
              let assump_37 := assump_2 assump_244
              cases assump_37
              case inl assump_53 =>
                cases assump_53
                case intro assump_55 assump_56 =>
                  cases assump_56
                  case intro assump_59 assump_60 =>
                    have assump_245 : p2 := by
                      exact assump_59
                    let assump_67 := assump_55 assump_245
                    apply False.elim assump_67
              case inr assump_54 =>
                cases assump_54
                case intro assump_71 assump_72 =>
                  cases assump_71
                  case intro assump_73 assump_74 =>
                    have assump_246 : p6 := by
                      exact assump_74
                    let assump_81 := assump_72 assump_246
                    apply False.elim assump_81
      case inr assump_9 =>
        cases assump_9
        case inl assump_85 =>
          cases assump_85
          case intro assump_87 assump_88 =>
            cases assump_7
            case inl assump_93 =>
              cases assump_93
              case intro assump_95 assump_96 =>
                have assump_247 : True := by
                  apply True.intro
                let assump_101 := assump_96 assump_247
                apply False.elim assump_101
            case inr assump_94 =>
              cases assump_94
              case intro assump_105 assump_106 =>
                cases assump_106
                case intro assump_109 assump_110 =>
                  have assump_248 : (((False → p2) ∧ (p3 ∧ p6)) → ((p2 → p2) → (p6 ∨ p0))) := by
                    intro assump_120
                    intro assump_121
                    cases assump_120
                    case intro assump_124 assump_125 =>
                      cases assump_125
                      case intro assump_128 assump_129 =>
                        apply Or.inl
                        exact assump_129
                  let assump_119 := assump_2 assump_248
                  cases assump_119
                  case inl assump_135 =>
                    cases assump_135
                    case intro assump_137 assump_138 =>
                      cases assump_138
                      case intro assump_141 assump_142 =>
                        have assump_249 : p2 := by
                          exact assump_141
                        let assump_149 := assump_137 assump_249
                        apply False.elim assump_149
                  case inr assump_136 =>
                    cases assump_136
                    case intro assump_153 assump_154 =>
                      cases assump_153
                      case intro assump_155 assump_156 =>
                        have assump_250 : p6 := by
                          exact assump_156
                        let assump_163 := assump_154 assump_250
                        apply False.elim assump_163
        case inr assump_86 =>
          cases assump_7
          case inl assump_169 =>
            cases assump_169
            case intro assump_171 assump_172 =>
              have assump_251 : True := by
                apply True.intro
              let assump_177 := assump_172 assump_251
              apply False.elim assump_177
          case inr assump_170 =>
            cases assump_170
            case intro assump_181 assump_182 =>
              cases assump_182
              case intro assump_185 assump_186 =>
                have assump_252 : (((False → p2) ∧ (p3 ∧ p6)) → ((p2 → p2) → (p6 ∨ p0))) := by
                  intro assump_196
                  intro assump_197
                  cases assump_196
                  case intro assump_200 assump_201 =>
                    cases assump_201
                    case intro assump_204 assump_205 =>
                      apply Or.inl
                      exact assump_205
                let assump_195 := assump_2 assump_252
                cases assump_195
                case inl assump_211 =>
                  cases assump_211
                  case intro assump_213 assump_214 =>
                    cases assump_214
                    case intro assump_217 assump_218 =>
                      have assump_253 : p2 := by
                        exact assump_217
                      let assump_225 := assump_213 assump_253
                      apply False.elim assump_225
                case inr assump_212 =>
                  cases assump_212
                  case intro assump_229 assump_230 =>
                    cases assump_229
                    case intro assump_231 assump_232 =>
                      have assump_254 : p6 := by
                        exact assump_232
                      let assump_239 := assump_230 assump_254
                      apply False.elim assump_239


variable (p3 p6 p1 p2 p4 p5 p7 p0 : Prop)
theorem file36_72831 : (((((False → p6) ∨ (p1 → p7)) ∨ ((p2 ∧ p6) ∨ (p1 ∧ p6))) ∨ (((p3 → False) → (p2 → False)) → False)) ∨ ((((p7 ∧ p0) ∨ (p7 ∨ p5)) ∧ ((p6 → False) ∧ (True → False))) → (((True ∧ True) ∨ (p5 ∨ p3)) ∨ ((p1 → p4) → (p2 → False))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply False.elim assump_1


variable (p1 p0 p2 p5 p7 p4 p3 p6 : Prop)
theorem file36_73234 : (((((p2 ∨ False) ∨ (True ∧ p7)) ∧ ((False ∨ p1) ∨ (p0 → False))) → (((True ∨ p1) → False) → ((p0 ∨ False) → (False → p4)))) → ((((p0 ∨ p6) ∧ (False → False)) ∧ ((p5 → p6) ∧ (True ∧ False))) → (((True → p0) → False) ∨ ((False ∧ p3) ∨ (p6 → False))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case inl assump_7 =>
        cases assump_4
        case intro assump_13 assump_14 =>
          cases assump_14
          case intro assump_17 assump_18 =>
            apply False.elim assump_18
      case inr assump_8 =>
        cases assump_4
        case intro assump_27 assump_28 =>
          cases assump_28
          case intro assump_31 assump_32 =>
            apply False.elim assump_32


variable (p2 p5 p6 p4 p0 p3 p1 : Prop)
theorem file36_74116 : ((((((p0 ∨ p0) → (p4 ∨ p1)) → False) ∧ (((p4 → p3) ∧ (p1 ∧ p3)) ∧ ((False ∧ False) ∧ (True → False)))) ∧ ((((p2 ∨ p6) → False) → False) ∧ (((p2 ∨ p4) ∨ (True → False)) ∧ ((p5 ∨ False) → False)))) → False) := by
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
              cases assump_20
              case intro assump_22 assump_23 =>
                apply False.elim assump_22


variable (p5 p3 p0 p2 p7 p6 p1 : Prop)
theorem file36_74901 : (((((False → False) ∧ (p5 → False)) ∧ ((False → False) ∨ (True ∧ p0))) ∧ (((True → p6) ∧ (p1 ∨ p0)) ∧ ((p2 → False) → (p1 ∨ False)))) → ((((False → p7) → (False → p1)) ∨ ((p0 ∨ True) ∨ (p2 ∧ p1))) → (((p0 → p3) → (p0 ∨ True)) ∨ ((False → False) → False)))) := by
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
          cases assump_10
          case inl assump_17 =>
            cases assump_8
            case intro assump_21 assump_22 =>
              cases assump_21
              case intro assump_23 assump_24 =>
                cases assump_24
                case inl assump_27 =>
                  apply Or.inl
                  intro assump_33
                  apply Or.inr
                  apply True.intro
                case inr assump_28 =>
                  apply Or.inl
                  intro assump_40
                  apply Or.inl
                  exact assump_28
          case inr assump_18 =>
            cases assump_18
            case intro assump_43 assump_44 =>
              cases assump_8
              case intro assump_49 assump_50 =>
                cases assump_49
                case intro assump_51 assump_52 =>
                  cases assump_52
                  case inl assump_55 =>
                    apply Or.inl
                    intro assump_61
                    apply Or.inl
                    exact assump_44
                  case inr assump_56 =>
                    apply Or.inl
                    intro assump_68
                    apply Or.inl
                    exact assump_56
  case inr assump_4 =>
    cases assump_4
    case inl assump_71 =>
      cases assump_71
      case inl assump_73 =>
        cases assump_1
        case intro assump_77 assump_78 =>
          cases assump_77
          case intro assump_79 assump_80 =>
            cases assump_79
            case intro assump_81 assump_82 =>
              cases assump_80
              case inl assump_87 =>
                cases assump_78
                case intro assump_91 assump_92 =>
                  cases assump_91
                  case intro assump_93 assump_94 =>
                    cases assump_94
                    case inl assump_97 =>
                      apply Or.inl
                      intro assump_103
                      apply Or.inl
                      exact assump_73
                    case inr assump_98 =>
                      apply Or.inl
                      intro assump_110
                      apply Or.inl
                      exact assump_98
              case inr assump_88 =>
                cases assump_88
                case intro assump_113 assump_114 =>
                  cases assump_78
                  case intro assump_119 assump_120 =>
                    cases assump_119
                    case intro assump_121 assump_122 =>
                      cases assump_122
                      case inl assump_125 =>
                        apply Or.inl
                        intro assump_131
                        apply Or.inl
                        exact assump_114
                      case inr assump_126 =>
                        apply Or.inl
                        intro assump_138
                        apply Or.inl
                        exact assump_126
      case inr assump_74 =>
        cases assump_1
        case intro assump_143 assump_144 =>
          cases assump_143
          case intro assump_145 assump_146 =>
            cases assump_145
            case intro assump_147 assump_148 =>
              cases assump_146
              case inl assump_153 =>
                cases assump_144
                case intro assump_157 assump_158 =>
                  cases assump_157
                  case intro assump_159 assump_160 =>
                    cases assump_160
                    case inl assump_163 =>
                      apply Or.inl
                      intro assump_169
                      apply Or.inr
                      apply True.intro
                    case inr assump_164 =>
                      apply Or.inl
                      intro assump_176
                      apply Or.inl
                      exact assump_164
              case inr assump_154 =>
                cases assump_154
                case intro assump_179 assump_180 =>
                  cases assump_144
                  case intro assump_185 assump_186 =>
                    cases assump_185
                    case intro assump_187 assump_188 =>
                      cases assump_188
                      case inl assump_191 =>
                        apply Or.inl
                        intro assump_197
                        apply Or.inl
                        exact assump_180
                      case inr assump_192 =>
                        apply Or.inl
                        intro assump_204
                        apply Or.inl
                        exact assump_192
    case inr assump_72 =>
      cases assump_72
      case intro assump_207 assump_208 =>
        cases assump_1
        case intro assump_213 assump_214 =>
          cases assump_213
          case intro assump_215 assump_216 =>
            cases assump_215
            case intro assump_217 assump_218 =>
              cases assump_216
              case inl assump_223 =>
                cases assump_214
                case intro assump_227 assump_228 =>
                  cases assump_227
                  case intro assump_229 assump_230 =>
                    cases assump_230
                    case inl assump_233 =>
                      apply Or.inl
                      intro assump_239
                      apply Or.inr
                      apply True.intro
                    case inr assump_234 =>
                      apply Or.inl
                      intro assump_246
                      apply Or.inl
                      exact assump_234
              case inr assump_224 =>
                cases assump_224
                case intro assump_249 assump_250 =>
                  cases assump_214
                  case intro assump_255 assump_256 =>
                    cases assump_255
                    case intro assump_257 assump_258 =>
                      cases assump_258
                      case inl assump_261 =>
                        apply Or.inl
                        intro assump_267
                        apply Or.inl
                        exact assump_250
                      case inr assump_262 =>
                        apply Or.inl
                        intro assump_274
                        apply Or.inl
                        exact assump_262


variable (p4 p0 p1 p7 p3 p5 : Prop)
theorem file36_81792 : (((((p4 → p1) → (False → False)) → False) → False) ∨ ((((p0 ∨ p0) ∨ (p7 → False)) ∨ ((False ∧ p3) ∧ (p1 → False))) ∨ (((p4 → p5) ∨ (p5 → False)) → False))) := by
  apply Or.inl
  intro assump_1
  have assump_12 : ((p4 → p1) → (False → False)) := by
    intro assump_5
    intro assump_6
    apply False.elim assump_6
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p6 p4 p2 p3 p0 p7 : Prop)
theorem file36_82234 : ((((((p0 ∧ p0) ∨ (p7 → True)) ∨ ((p3 ∨ p2) ∨ (p0 ∧ True))) → False) ∨ ((((p6 ∧ True) ∨ (p3 → p4)) → ((p7 ∨ p7) → (p7 ∧ p7))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_71 : (((p0 ∧ p0) ∨ (p7 → True)) ∨ ((p3 ∨ p2) ∨ (p0 ∧ True))) := by
      apply Or.inl
      apply Or.inr
      intro assump_7
      apply True.intro
    let assump_6 := assump_2 assump_71
    apply False.elim assump_6
  case inr assump_3 =>
    have assump_72 : (((p6 ∧ True) ∨ (p3 → p4)) → ((p7 ∨ p7) → (p7 ∧ p7))) := by
      intro assump_14
      intro assump_15
      apply And.intro
      cases assump_15
      case inl assump_16 =>
        cases assump_14
        case inl assump_20 =>
          cases assump_20
          case intro assump_22 assump_23 =>
            exact assump_16
        case inr assump_21 =>
          exact assump_16
      case inr assump_17 =>
        cases assump_14
        case inl assump_32 =>
          cases assump_32
          case intro assump_34 assump_35 =>
            exact assump_17
        case inr assump_33 =>
          exact assump_17
      cases assump_15
      case inl assump_42 =>
        cases assump_14
        case inl assump_46 =>
          cases assump_46
          case intro assump_48 assump_49 =>
            exact assump_42
        case inr assump_47 =>
          exact assump_42
      case inr assump_43 =>
        cases assump_14
        case inl assump_58 =>
          cases assump_58
          case intro assump_60 assump_61 =>
            exact assump_43
        case inr assump_59 =>
          exact assump_43
    let assump_13 := assump_3 assump_72
    apply False.elim assump_13


variable (p2 p3 p7 p4 p6 p0 : Prop)
theorem file36_83964 : ((((((p6 ∨ p4) → (p7 ∧ p7)) → False) → (((False ∧ p4) → (p2 → p3)) ∨ ((p7 → False) ∧ (p2 → p0)))) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p6 ∨ p4) → (p7 ∧ p7)) → False) → (((False ∧ p4) → (p2 → p3)) ∨ ((p7 → False) ∧ (p2 → p0)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    intro assump_9
    cases assump_8
    case intro assump_12 assump_13 =>
      apply False.elim assump_12
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p6 p2 p5 p0 p4 p7 p1 : Prop)
theorem file36_84516 : ((((((p5 → p6) ∧ (p1 → False)) ∨ ((p6 ∨ p7) → (p4 → p5))) → (((p0 → False) ∨ (p2 → p4)) ∨ ((p6 → False) → (p6 ∨ p5)))) ∧ ((((p2 → p5) → (p1 ∧ p7)) ∨ ((p2 ∧ p6) → False)) ∧ (((p1 ∧ True) ∨ (p1 → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        have assump_42 : ((p1 ∧ True) ∨ (p1 → False)) := by
          apply Or.inr
          intro assump_15
          have assump_43 : ((p1 ∧ True) ∨ (p1 → False)) := by
            apply Or.inl
            apply And.intro
            exact assump_15
            apply True.intro
          let assump_19 := assump_7 assump_43
          apply False.elim assump_19
        let assump_14 := assump_7 assump_42
        apply False.elim assump_14
      case inr assump_9 =>
        have assump_44 : ((p1 ∧ True) ∨ (p1 → False)) := by
          apply Or.inr
          intro assump_31
          have assump_45 : ((p1 ∧ True) ∨ (p1 → False)) := by
            apply Or.inl
            apply And.intro
            exact assump_31
            apply True.intro
          let assump_35 := assump_7 assump_45
          apply False.elim assump_35
        let assump_30 := assump_7 assump_44
        apply False.elim assump_30


variable (p4 p1 p3 p0 p2 p5 p6 : Prop)
theorem file36_85891 : (((((p6 → False) → (p6 → False)) ∨ ((False ∨ p3) ∧ (p1 → False))) ∧ (((p3 ∧ p0) → (p0 ∨ True)) → False)) → ((((p1 → p4) ∨ (p0 ∧ p3)) ∧ ((p6 ∨ p5) → (p2 → p1))) → (((p2 ∨ p1) → False) → ((p1 → p4) → False)))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_2
  case intro assump_9 assump_10 =>
    cases assump_9
    case inl assump_11 =>
      cases assump_1
      case intro assump_17 assump_18 =>
        cases assump_17
        case inl assump_19 =>
          have assump_109 : ((p3 ∧ p0) → (p0 ∨ True)) := by
            intro assump_26
            cases assump_26
            case intro assump_27 assump_28 =>
              apply Or.inl
              exact assump_28
          let assump_25 := assump_18 assump_109
          apply False.elim assump_25
        case inr assump_20 =>
          cases assump_20
          case intro assump_36 assump_37 =>
            cases assump_36
            case inl assump_38 =>
              apply False.elim assump_38
            case inr assump_39 =>
              have assump_110 : ((p3 ∧ p0) → (p0 ∨ True)) := by
                intro assump_49
                cases assump_49
                case intro assump_50 assump_51 =>
                  apply Or.inl
                  exact assump_51
              let assump_48 := assump_18 assump_110
              apply False.elim assump_48
    case inr assump_12 =>
      cases assump_12
      case intro assump_59 assump_60 =>
        cases assump_1
        case intro assump_67 assump_68 =>
          cases assump_67
          case inl assump_69 =>
            have assump_111 : ((p3 ∧ p0) → (p0 ∨ True)) := by
              intro assump_76
              cases assump_76
              case intro assump_77 assump_78 =>
                apply Or.inl
                exact assump_78
            let assump_75 := assump_68 assump_111
            apply False.elim assump_75
          case inr assump_70 =>
            cases assump_70
            case intro assump_86 assump_87 =>
              cases assump_86
              case inl assump_88 =>
                apply False.elim assump_88
              case inr assump_89 =>
                have assump_112 : ((p3 ∧ p0) → (p0 ∨ True)) := by
                  intro assump_99
                  cases assump_99
                  case intro assump_100 assump_101 =>
                    apply Or.inl
                    exact assump_101
                let assump_98 := assump_68 assump_112
                apply False.elim assump_98


variable (p3 p2 p0 p6 p5 p4 p7 p1 : Prop)
theorem file36_88465 : (((((p6 ∨ False) → (p7 → p3)) → False) ∧ (((False ∨ p0) ∧ (p3 ∧ p2)) ∨ ((p3 ∨ p0) ∧ (p5 → False)))) → ((((p1 ∨ p0) → (False → False)) → ((p1 ∨ p3) ∨ (p4 → p4))) ∧ (((p5 ∧ True) ∧ (p3 ∧ p7)) → ((p3 ∨ p7) ∧ (p4 ∨ p3))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case inl assump_9 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_11
        case inl assump_13 =>
          apply False.elim assump_13
        case inr assump_14 =>
          cases assump_12
          case intro assump_19 assump_20 =>
            apply Or.inl
            apply Or.inr
            exact assump_19
    case inr assump_10 =>
      cases assump_10
      case intro assump_25 assump_26 =>
        cases assump_25
        case inl assump_27 =>
          apply Or.inl
          apply Or.inr
          exact assump_27
        case inr assump_28 =>
          apply Or.inr
          intro assump_37
          exact assump_37
  intro assump_40
  apply And.intro
  cases assump_40
  case intro assump_41 assump_42 =>
    cases assump_41
    case intro assump_43 assump_44 =>
      cases assump_42
      case intro assump_49 assump_50 =>
        cases assump_1
        case intro assump_55 assump_56 =>
          cases assump_56
          case inl assump_59 =>
            cases assump_59
            case intro assump_61 assump_62 =>
              cases assump_61
              case inl assump_63 =>
                apply False.elim assump_63
              case inr assump_64 =>
                cases assump_62
                case intro assump_69 assump_70 =>
                  apply Or.inl
                  exact assump_69
          case inr assump_60 =>
            cases assump_60
            case intro assump_75 assump_76 =>
              cases assump_75
              case inl assump_77 =>
                apply Or.inl
                exact assump_77
              case inr assump_78 =>
                apply Or.inl
                exact assump_49
  cases assump_40
  case intro assump_87 assump_88 =>
    cases assump_87
    case intro assump_89 assump_90 =>
      cases assump_88
      case intro assump_95 assump_96 =>
        cases assump_1
        case intro assump_101 assump_102 =>
          cases assump_102
          case inl assump_105 =>
            cases assump_105
            case intro assump_107 assump_108 =>
              cases assump_107
              case inl assump_109 =>
                apply False.elim assump_109
              case inr assump_110 =>
                cases assump_108
                case intro assump_115 assump_116 =>
                  apply Or.inr
                  exact assump_115
          case inr assump_106 =>
            cases assump_106
            case intro assump_121 assump_122 =>
              cases assump_121
              case inl assump_123 =>
                apply Or.inr
                exact assump_123
              case inr assump_124 =>
                apply Or.inr
                exact assump_95


variable (p3 p2 p6 p7 p4 p0 p5 : Prop)
theorem file36_91594 : (((((p0 → False) → (False ∧ p4)) → False) ∧ (((p3 ∧ p7) ∨ (p5 ∨ p0)) ∧ ((p6 ∨ p2) ∧ (p3 → False)))) → ((((p5 ∧ p5) ∨ (p0 → False)) ∨ ((p3 → True) ∨ (p3 ∧ p2))) ∨ (((False ∨ p3) → False) ∨ ((p2 → False) → (True → False))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_7
          case intro assump_16 assump_17 =>
            cases assump_16
            case inl assump_18 =>
              apply Or.inl
              apply Or.inl
              apply Or.inr
              intro assump_24
              have assump_122 : p3 := by
                exact assump_10
              let assump_28 := assump_17 assump_122
              apply False.elim assump_28
            case inr assump_19 =>
              apply Or.inl
              apply Or.inl
              apply Or.inr
              intro assump_36
              have assump_123 : p3 := by
                exact assump_10
              let assump_40 := assump_17 assump_123
              apply False.elim assump_40
      case inr assump_9 =>
        cases assump_9
        case inl assump_44 =>
          cases assump_7
          case intro assump_48 assump_49 =>
            cases assump_48
            case inl assump_50 =>
              apply Or.inl
              apply Or.inl
              apply Or.inl
              apply And.intro
              exact assump_44
              exact assump_44
            case inr assump_51 =>
              apply Or.inl
              apply Or.inl
              apply Or.inl
              apply And.intro
              exact assump_44
              exact assump_44
        case inr assump_45 =>
          cases assump_7
          case intro assump_62 assump_63 =>
            cases assump_62
            case inl assump_64 =>
              apply Or.inl
              apply Or.inl
              apply Or.inr
              intro assump_70
              have assump_124 : ((p0 → False) → (False ∧ p4)) := by
                intro assump_78
                apply And.intro
                have assump_125 : p0 := by
                  exact assump_70
                let assump_81 := assump_78 assump_125
                apply False.elim assump_81
                have assump_126 : p0 := by
                  exact assump_70
                let assump_87 := assump_78 assump_126
                apply False.elim assump_87
              let assump_77 := assump_2 assump_124
              apply False.elim assump_77
            case inr assump_65 =>
              apply Or.inl
              apply Or.inl
              apply Or.inr
              intro assump_98
              have assump_127 : ((p0 → False) → (False ∧ p4)) := by
                intro assump_106
                apply And.intro
                have assump_128 : p0 := by
                  exact assump_98
                let assump_109 := assump_106 assump_128
                apply False.elim assump_109
                have assump_129 : p0 := by
                  exact assump_98
                let assump_115 := assump_106 assump_129
                apply False.elim assump_115
              let assump_105 := assump_2 assump_127
              apply False.elim assump_105


variable (p7 p4 p6 p5 : Prop)
theorem file36_94989 : ((((((False → p5) ∨ (p4 → False)) → False) → (((p7 ∧ p6) ∨ (p6 → False)) → False)) → False) → False) := by
  intro assump_1
  have assump_38 : ((((False → p5) ∨ (p4 → False)) → False) → (((p7 ∧ p6) ∨ (p6 → False)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        have assump_39 : ((False → p5) ∨ (p4 → False)) := by
          apply Or.inl
          intro assump_18
          apply False.elim assump_18
        let assump_17 := assump_5 assump_39
        apply False.elim assump_17
    case inr assump_8 =>
      have assump_40 : ((False → p5) ∨ (p4 → False)) := by
        apply Or.inl
        intro assump_29
        apply False.elim assump_29
      let assump_28 := assump_5 assump_40
      apply False.elim assump_28
  let assump_4 := assump_1 assump_38
  apply False.elim assump_4


variable (p0 p3 p1 p4 p6 : Prop)
theorem file36_95948 : ((((((True ∧ True) → False) → ((p0 ∧ p4) ∨ (p3 ∨ p4))) ∨ (((False ∨ p4) → (True → False)) ∧ ((p1 ∨ p3) ∨ (p6 → p1)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((True ∧ True) → False) → ((p0 ∧ p4) ∨ (p3 ∨ p4))) ∨ (((False ∨ p4) → (True → False)) ∧ ((p1 ∨ p3) ∨ (p6 → p1)))) := by
    apply Or.inl
    intro assump_5
    have assump_16 : (True ∧ True) := by
      apply And.intro
      apply True.intro
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p3 p2 p7 p1 p4 p0 : Prop)
theorem file36_96587 : ((((((p2 ∧ p2) → False) → False) ∨ (((p4 ∨ p7) → False) ∧ ((p4 ∧ p2) → False))) ∧ ((((False → p7) ∧ (p1 → False)) → False) ∧ (((p1 ∧ True) ∧ (p1 → False)) ∧ ((p0 ∧ p2) ∧ (p3 ∧ p3))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              cases assump_13
              case intro assump_24 assump_25 =>
                cases assump_24
                case intro assump_26 assump_27 =>
                  cases assump_25
                  case intro assump_32 assump_33 =>
                    have assump_90 : p1 := by
                      exact assump_16
                    let assump_42 := assump_15 assump_90
                    apply False.elim assump_42
    case inr assump_5 =>
      cases assump_5
      case intro assump_46 assump_47 =>
        cases assump_3
        case intro assump_52 assump_53 =>
          cases assump_53
          case intro assump_56 assump_57 =>
            cases assump_56
            case intro assump_58 assump_59 =>
              cases assump_58
              case intro assump_60 assump_61 =>
                cases assump_57
                case intro assump_68 assump_69 =>
                  cases assump_68
                  case intro assump_70 assump_71 =>
                    cases assump_69
                    case intro assump_76 assump_77 =>
                      have assump_91 : p1 := by
                        exact assump_60
                      let assump_86 := assump_59 assump_91
                      apply False.elim assump_86


variable (p7 p2 p0 p5 p1 p6 p3 : Prop)
theorem file36_98490 : (((((p1 → p7) ∨ (True ∧ False)) ∧ ((p3 ∨ p2) → (p3 ∨ p1))) → False) → ((((p5 ∨ True) → False) → False) ∨ (((False → False) → (True ∧ False)) → ((p6 → False) ∨ (p0 ∧ True))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_11 : (p5 ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_7 := assump_4 assump_11
  apply False.elim assump_7


variable (p5 p0 p3 p6 p1 : Prop)
theorem file36_98917 : ((((((True ∧ p3) → False) → ((p5 → p0) ∨ (p3 → True))) → (((p0 ∧ p6) → (p1 ∨ True)) ∨ ((p0 ∧ p0) → False))) → False) → False) := by
  intro assump_53
  have assump_70 : ((((True ∧ p3) → False) → ((p5 → p0) ∨ (p3 → True))) → (((p0 ∧ p6) → (p1 ∨ True)) ∨ ((p0 ∧ p0) → False))) := by
    intro assump_57
    apply Or.inl
    intro assump_60
    cases assump_60
    case intro assump_61 assump_62 =>
      apply Or.inr
      apply True.intro
  let assump_56 := assump_53 assump_70
  apply False.elim assump_56


variable (p4 p6 p0 p3 p2 p1 p7 : Prop)
theorem file36_99486 : (((((p4 ∨ True) ∨ (p7 ∧ p1)) ∨ ((p0 → p1) ∨ (p0 → True))) → False) → ((((p3 → False) → False) → ((p4 → p2) ∨ (True ∨ p6))) → False)) := by
  intro assump_1
  intro assump_2
  have assump_11 : (((p4 ∨ True) ∨ (p7 ∧ p1)) ∨ ((p0 → p1) ∨ (p0 → True))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_7 := assump_1 assump_11
  apply False.elim assump_7


variable (p0 p1 p7 p6 : Prop)
theorem file36_99931 : (((((p0 ∨ False) ∨ (p6 ∨ p1)) → False) ∧ (((False → True) → False) ∧ ((p6 ∨ p1) ∧ (p7 ∧ p1)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          cases assump_11
          case intro assump_16 assump_17 =>
            have assump_46 : (False → True) := by
              intro assump_26
              apply True.intro
            let assump_25 := assump_6 assump_46
            apply False.elim assump_25
        case inr assump_13 =>
          cases assump_11
          case intro assump_32 assump_33 =>
            have assump_47 : (False → True) := by
              intro assump_42
              apply True.intro
            let assump_41 := assump_6 assump_47
            apply False.elim assump_41


variable (p6 p4 p1 : Prop)
theorem file36_100896 : (((((False → False) ∧ (p4 → False)) → ((p4 → False) → False)) ∧ (((p6 ∨ p4) → False) ∧ ((p6 ∨ p1) ∨ (False → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        cases assump_10
        case inl assump_12 =>
          have assump_81 : (p6 ∨ p4) := by
            apply Or.inl
            exact assump_12
          let assump_17 := assump_6 assump_81
          apply False.elim assump_17
        case inr assump_13 =>
          have assump_82 : ((False → False) ∧ (p4 → False)) := by
            apply And.intro
            intro assump_26
            apply False.elim assump_26
            intro assump_29
            have assump_83 : (p6 ∨ p4) := by
              apply Or.inr
              exact assump_29
            let assump_34 := assump_6 assump_83
            apply False.elim assump_34
          let assump_25 := assump_2 assump_82
          have assump_84 : (p4 → False) := by
            intro assump_39
            have assump_85 : (p6 ∨ p4) := by
              apply Or.inr
              exact assump_39
            let assump_44 := assump_6 assump_85
            apply False.elim assump_44
          let assump_38 := assump_25 assump_84
          apply False.elim assump_38
      case inr assump_11 =>
        have assump_86 : ((False → False) ∧ (p4 → False)) := by
          apply And.intro
          intro assump_56
          apply False.elim assump_56
          intro assump_59
          have assump_87 : (p6 ∨ p4) := by
            apply Or.inr
            exact assump_59
          let assump_64 := assump_6 assump_87
          apply False.elim assump_64
        let assump_55 := assump_2 assump_86
        have assump_88 : (p4 → False) := by
          intro assump_69
          have assump_89 : (p6 ∨ p4) := by
            apply Or.inr
            exact assump_69
          let assump_74 := assump_6 assump_89
          apply False.elim assump_74
        let assump_68 := assump_55 assump_88
        apply False.elim assump_68


variable (p7 p3 p2 p0 p6 p4 p5 : Prop)
theorem file36_103058 : ((((((p3 ∧ p3) ∧ (p0 ∨ p4)) → False) → False) ∧ ((((p6 → p5) → (False ∨ p7)) ∧ ((False ∨ True) → (p5 → p2))) ∧ (((p4 ∨ p3) → False) ∧ ((p5 ∨ False) ∧ (False ∧ p0))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case intro assump_14 assump_15 =>
          cases assump_15
          case intro assump_18 assump_19 =>
            cases assump_18
            case inl assump_20 =>
              cases assump_19
              case intro assump_24 assump_25 =>
                apply False.elim assump_24
            case inr assump_21 =>
              apply False.elim assump_21


variable (p6 p2 p5 p3 : Prop)
theorem file36_103869 : ((((((p2 ∧ p2) ∧ (False ∨ p2)) ∧ ((p3 → False) ∧ (True ∨ p5))) ∨ (((p5 ∨ p6) → False) → False)) ∧ ((((True → p2) ∧ (True → False)) → ((True → False) ∧ (True ∨ p2))) → False)) → False) := by
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
          case intro assump_10 assump_11 =>
            cases assump_9
            case inl assump_16 =>
              apply False.elim assump_16
            case inr assump_17 =>
              cases assump_7
              case intro assump_22 assump_23 =>
                cases assump_23
                case inl assump_26 =>
                  have assump_112 : (((True → p2) ∧ (True → False)) → ((True → False) ∧ (True ∨ p2))) := by
                    intro assump_33
                    apply And.intro
                    intro assump_34
                    cases assump_33
                    case intro assump_37 assump_38 =>
                      have assump_113 : True := by
                        apply True.intro
                      let assump_43 := assump_38 assump_113
                      apply False.elim assump_43
                    cases assump_33
                    case intro assump_47 assump_48 =>
                      apply Or.inl
                      apply True.intro
                  let assump_32 := assump_3 assump_112
                  apply False.elim assump_32
                case inr assump_27 =>
                  have assump_114 : (((True → p2) ∧ (True → False)) → ((True → False) ∧ (True ∨ p2))) := by
                    intro assump_61
                    apply And.intro
                    intro assump_62
                    cases assump_61
                    case intro assump_65 assump_66 =>
                      have assump_115 : True := by
                        apply True.intro
                      let assump_71 := assump_66 assump_115
                      apply False.elim assump_71
                    cases assump_61
                    case intro assump_75 assump_76 =>
                      apply Or.inl
                      apply True.intro
                  let assump_60 := assump_3 assump_114
                  apply False.elim assump_60
    case inr assump_5 =>
      have assump_116 : (((True → p2) ∧ (True → False)) → ((True → False) ∧ (True ∨ p2))) := by
        intro assump_89
        apply And.intro
        intro assump_90
        cases assump_89
        case intro assump_93 assump_94 =>
          have assump_117 : True := by
            apply True.intro
          let assump_99 := assump_94 assump_117
          apply False.elim assump_99
        cases assump_89
        case intro assump_103 assump_104 =>
          apply Or.inl
          apply True.intro
      let assump_88 := assump_3 assump_116
      apply False.elim assump_88


variable (p3 p0 p6 p1 p4 p7 : Prop)
theorem file36_106891 : (((((False → False) ∨ (p7 → False)) ∨ ((p4 ∨ p0) ∨ (p4 ∧ p7))) → False) → ((((p3 ∧ p6) → (False → p1)) → False) → (((p0 ∨ False) → False) → ((True → p0) → False)))) := by
  intro assump_13
  intro assump_14
  intro assump_15
  intro assump_16
  have assump_32 : (((False → False) ∨ (p7 → False)) ∨ ((p4 ∨ p0) ∨ (p4 ∧ p7))) := by
    apply Or.inl
    apply Or.inl
    intro assump_26
    apply False.elim assump_26
  let assump_25 := assump_13 assump_32
  apply False.elim assump_25


variable (p4 p2 p5 p1 p6 p7 p3 : Prop)
theorem file36_107436 : ((((((False → False) ∨ (p2 ∧ p3)) ∨ ((p2 ∨ p3) → (p7 → p6))) ∧ (((p3 ∨ p2) ∨ (p3 ∨ p1)) ∨ ((p2 ∧ p6) ∧ (p5 → False)))) ∧ ((((p4 → p7) → False) → False) ∧ (((False → p1) ∨ (False → False)) → False))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_8
      case inl assump_10 =>
        cases assump_10
        case inl assump_12 =>
          cases assump_9
          case inl assump_16 =>
            cases assump_16
            case inl assump_18 =>
              cases assump_18
              case inl assump_20 =>
                cases assump_7
                case intro assump_24 assump_25 =>
                  have assump_297 : ((False → p1) ∨ (False → False)) := by
                    apply Or.inl
                    intro assump_31
                    apply False.elim assump_31
                  let assump_30 := assump_25 assump_297
                  apply False.elim assump_30
              case inr assump_21 =>
                cases assump_7
                case intro assump_39 assump_40 =>
                  have assump_298 : ((False → p1) ∨ (False → False)) := by
                    apply Or.inl
                    intro assump_46
                    apply False.elim assump_46
                  let assump_45 := assump_40 assump_298
                  apply False.elim assump_45
            case inr assump_19 =>
              cases assump_19
              case inl assump_52 =>
                cases assump_7
                case intro assump_56 assump_57 =>
                  have assump_299 : ((False → p1) ∨ (False → False)) := by
                    apply Or.inl
                    intro assump_63
                    apply False.elim assump_63
                  let assump_62 := assump_57 assump_299
                  apply False.elim assump_62
              case inr assump_53 =>
                cases assump_7
                case intro assump_71 assump_72 =>
                  have assump_300 : ((False → p1) ∨ (False → False)) := by
                    apply Or.inl
                    intro assump_78
                    apply False.elim assump_78
                  let assump_77 := assump_72 assump_300
                  apply False.elim assump_77
          case inr assump_17 =>
            cases assump_17
            case intro assump_84 assump_85 =>
              cases assump_84
              case intro assump_86 assump_87 =>
                cases assump_7
                case intro assump_94 assump_95 =>
                  have assump_301 : ((False → p1) ∨ (False → False)) := by
                    apply Or.inl
                    intro assump_101
                    apply False.elim assump_101
                  let assump_100 := assump_95 assump_301
                  apply False.elim assump_100
        case inr assump_13 =>
          cases assump_13
          case intro assump_107 assump_108 =>
            cases assump_9
            case inl assump_113 =>
              cases assump_113
              case inl assump_115 =>
                cases assump_115
                case inl assump_117 =>
                  cases assump_7
                  case intro assump_121 assump_122 =>
                    have assump_302 : ((False → p1) ∨ (False → False)) := by
                      apply Or.inl
                      intro assump_128
                      apply False.elim assump_128
                    let assump_127 := assump_122 assump_302
                    apply False.elim assump_127
                case inr assump_118 =>
                  cases assump_7
                  case intro assump_136 assump_137 =>
                    have assump_303 : ((False → p1) ∨ (False → False)) := by
                      apply Or.inl
                      intro assump_143
                      apply False.elim assump_143
                    let assump_142 := assump_137 assump_303
                    apply False.elim assump_142
              case inr assump_116 =>
                cases assump_116
                case inl assump_149 =>
                  cases assump_7
                  case intro assump_153 assump_154 =>
                    have assump_304 : ((False → p1) ∨ (False → False)) := by
                      apply Or.inl
                      intro assump_160
                      apply False.elim assump_160
                    let assump_159 := assump_154 assump_304
                    apply False.elim assump_159
                case inr assump_150 =>
                  cases assump_7
                  case intro assump_168 assump_169 =>
                    have assump_305 : ((False → p1) ∨ (False → False)) := by
                      apply Or.inl
                      intro assump_175
                      apply False.elim assump_175
                    let assump_174 := assump_169 assump_305
                    apply False.elim assump_174
            case inr assump_114 =>
              cases assump_114
              case intro assump_181 assump_182 =>
                cases assump_181
                case intro assump_183 assump_184 =>
                  cases assump_7
                  case intro assump_191 assump_192 =>
                    have assump_306 : ((False → p1) ∨ (False → False)) := by
                      apply Or.inl
                      intro assump_198
                      apply False.elim assump_198
                    let assump_197 := assump_192 assump_306
                    apply False.elim assump_197
      case inr assump_11 =>
        cases assump_9
        case inl assump_206 =>
          cases assump_206
          case inl assump_208 =>
            cases assump_208
            case inl assump_210 =>
              cases assump_7
              case intro assump_214 assump_215 =>
                have assump_307 : ((False → p1) ∨ (False → False)) := by
                  apply Or.inl
                  intro assump_221
                  apply False.elim assump_221
                let assump_220 := assump_215 assump_307
                apply False.elim assump_220
            case inr assump_211 =>
              cases assump_7
              case intro assump_229 assump_230 =>
                have assump_308 : ((False → p1) ∨ (False → False)) := by
                  apply Or.inl
                  intro assump_236
                  apply False.elim assump_236
                let assump_235 := assump_230 assump_308
                apply False.elim assump_235
          case inr assump_209 =>
            cases assump_209
            case inl assump_242 =>
              cases assump_7
              case intro assump_246 assump_247 =>
                have assump_309 : ((False → p1) ∨ (False → False)) := by
                  apply Or.inl
                  intro assump_253
                  apply False.elim assump_253
                let assump_252 := assump_247 assump_309
                apply False.elim assump_252
            case inr assump_243 =>
              cases assump_7
              case intro assump_261 assump_262 =>
                have assump_310 : ((False → p1) ∨ (False → False)) := by
                  apply Or.inl
                  intro assump_268
                  apply False.elim assump_268
                let assump_267 := assump_262 assump_310
                apply False.elim assump_267
        case inr assump_207 =>
          cases assump_207
          case intro assump_274 assump_275 =>
            cases assump_274
            case intro assump_276 assump_277 =>
              cases assump_7
              case intro assump_284 assump_285 =>
                have assump_311 : ((False → p1) ∨ (False → False)) := by
                  apply Or.inl
                  intro assump_291
                  apply False.elim assump_291
                let assump_290 := assump_285 assump_311
                apply False.elim assump_290


variable (p3 p0 p1 p2 p4 p6 p7 p5 : Prop)
theorem file36_115398 : ((((((p5 ∧ p0) ∨ (p4 ∨ p5)) → ((p1 ∧ p4) ∨ (p4 ∨ p6))) ∧ (((p4 → p3) ∨ (p7 → p4)) → False)) ∧ ((((p7 ∧ p2) ∧ (p4 ∧ p1)) ∨ ((p3 ∧ True) ∨ (p7 → False))) ∧ (((True ∨ p1) ∨ (False ∧ False)) → False))) → False) := by
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
          case intro assump_14 assump_15 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              cases assump_15
              case intro assump_22 assump_23 =>
                have assump_56 : ((True ∨ p1) ∨ (False ∧ False)) := by
                  apply Or.inl
                  apply Or.inl
                  apply True.intro
                let assump_30 := assump_11 assump_56
                apply False.elim assump_30
        case inr assump_13 =>
          cases assump_13
          case inl assump_34 =>
            cases assump_34
            case intro assump_36 assump_37 =>
              have assump_57 : ((True ∨ p1) ∨ (False ∧ False)) := by
                apply Or.inl
                apply Or.inl
                apply True.intro
              let assump_44 := assump_11 assump_57
              apply False.elim assump_44
          case inr assump_35 =>
            have assump_58 : ((True ∨ p1) ∨ (False ∧ False)) := by
              apply Or.inl
              apply Or.inl
              apply True.intro
            let assump_52 := assump_11 assump_58
            apply False.elim assump_52


variable (p2 p7 p6 p1 p3 p4 p5 : Prop)
theorem file36_117084 : (((((p2 → p6) ∨ (p7 → p3)) → False) → (((p6 → False) ∨ (p5 → False)) ∧ ((p7 ∨ False) ∨ (p6 → False)))) ∨ ((((p2 → p3) → (p7 → p4)) → ((False ∨ p7) ∨ (False ∧ p1))) ∨ (((False ∧ p2) ∧ (p1 ∨ p4)) ∨ ((p5 → False) → False)))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  apply Or.inl
  intro assump_4
  have assump_28 : ((p2 → p6) ∨ (p7 → p3)) := by
    apply Or.inl
    intro assump_9
    exact assump_4
  let assump_8 := assump_1 assump_28
  apply False.elim assump_8
  apply Or.inr
  intro assump_17
  have assump_29 : ((p2 → p6) ∨ (p7 → p3)) := by
    apply Or.inl
    intro assump_22
    exact assump_17
  let assump_21 := assump_1 assump_29
  apply False.elim assump_21


variable (p2 : Prop)
theorem file36_117814 : ((((((True ∧ True) ∧ (False → p2)) → False) → False) → False) → False) := by
  intro assump_20
  have assump_37 : ((((True ∧ True) ∧ (False → p2)) → False) → False) := by
    intro assump_24
    have assump_38 : ((True ∧ True) ∧ (False → p2)) := by
      apply And.intro
      apply And.intro
      apply True.intro
      apply True.intro
      intro assump_28
      apply False.elim assump_28
    let assump_27 := assump_24 assump_38
    apply False.elim assump_27
  let assump_23 := assump_20 assump_37
  apply False.elim assump_23


variable (p2 p5 p0 p3 p7 p4 p1 : Prop)
theorem file36_118411 : (((((p1 ∨ False) ∧ (p7 ∧ p1)) ∧ ((p2 → True) → False)) ∧ (((p4 ∧ p0) → (p5 → False)) ∧ ((p3 ∨ p5) ∨ (p7 → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_7
          case intro assump_12 assump_13 =>
            cases assump_3
            case intro assump_20 assump_21 =>
              cases assump_21
              case inl assump_24 =>
                cases assump_24
                case inl assump_26 =>
                  have assump_54 : (p2 → True) := by
                    intro assump_33
                    apply True.intro
                  let assump_32 := assump_5 assump_54
                  apply False.elim assump_32
                case inr assump_27 =>
                  have assump_55 : (p2 → True) := by
                    intro assump_42
                    apply True.intro
                  let assump_41 := assump_5 assump_55
                  apply False.elim assump_41
              case inr assump_25 =>
                have assump_56 : p7 := by
                  exact assump_12
                let assump_48 := assump_25 assump_56
                apply False.elim assump_48
        case inr assump_9 =>
          apply False.elim assump_9


variable (p0 p2 p3 p1 p5 : Prop)
theorem file36_119872 : (((((True → False) → False) → False) → False) ∨ ((((True → False) → (p2 → p3)) → False) ∨ (((p0 ∨ p2) → False) ∨ ((p1 → p1) ∧ (p5 → False))))) := by
  apply Or.inl
  intro assump_1
  have assump_15 : ((True → False) → False) := by
    intro assump_5
    have assump_16 : True := by
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p7 p4 p0 : Prop)
theorem file36_120362 : ((((((p0 ∧ False) ∧ (True → False)) → ((p7 ∨ p7) → (True ∧ True))) ∨ (((p7 ∨ False) ∨ (p4 → False)) ∨ ((p4 ∨ True) → False))) → False) → False) := by
  intro assump_19
  have assump_28 : ((((p0 ∧ False) ∧ (True → False)) → ((p7 ∨ p7) → (True ∧ True))) ∨ (((p7 ∨ False) ∨ (p4 → False)) ∨ ((p4 ∨ True) → False))) := by
    apply Or.inl
    intro assump_23
    intro assump_24
    apply And.intro
    apply True.intro
    apply True.intro
  let assump_22 := assump_19 assump_28
  apply False.elim assump_22


variable (p5 p7 p3 p6 p4 : Prop)
theorem file36_120923 : ((((((p4 ∧ p3) ∨ (p5 ∨ p5)) ∨ ((p7 → False) → False)) → False) ∧ ((((p6 ∨ p4) ∨ (p6 → False)) ∨ ((p3 → False) → (p6 ∧ False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_20 : (((p6 ∨ p4) ∨ (p6 → False)) ∨ ((p3 → False) → (p6 ∧ False))) := by
      apply Or.inl
      apply Or.inr
      intro assump_9
      have assump_21 : (((p6 ∨ p4) ∨ (p6 → False)) ∨ ((p3 → False) → (p6 ∧ False))) := by
        apply Or.inl
        apply Or.inl
        apply Or.inl
        exact assump_9
      let assump_13 := assump_3 assump_21
      apply False.elim assump_13
    let assump_8 := assump_3 assump_20
    apply False.elim assump_8


variable (p4 p3 p2 p0 p7 p6 p1 p5 : Prop)
theorem file36_121676 : (((((p6 → False) → False) → False) ∧ (((p2 ∨ p4) ∨ (p7 → p5)) ∧ ((p1 → False) ∧ (True → False)))) → ((((False → False) → False) → ((p5 ∨ p1) → False)) ∨ (((p3 ∨ p1) ∨ (p0 → False)) ∨ ((p3 → False) → False)))) := by
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
            apply Or.inl
            intro assump_20
            intro assump_21
            cases assump_21
            case inl assump_22 =>
              have assump_114 : (False → False) := by
                intro assump_29
                apply False.elim assump_29
              let assump_28 := assump_20 assump_114
              apply False.elim assump_28
            case inr assump_23 =>
              have assump_115 : (False → False) := by
                intro assump_40
                apply False.elim assump_40
              let assump_39 := assump_20 assump_115
              apply False.elim assump_39
        case inr assump_11 =>
          cases assump_7
          case intro assump_48 assump_49 =>
            apply Or.inl
            intro assump_54
            intro assump_55
            cases assump_55
            case inl assump_56 =>
              have assump_116 : (False → False) := by
                intro assump_63
                apply False.elim assump_63
              let assump_62 := assump_54 assump_116
              apply False.elim assump_62
            case inr assump_57 =>
              have assump_117 : (False → False) := by
                intro assump_74
                apply False.elim assump_74
              let assump_73 := assump_54 assump_117
              apply False.elim assump_73
      case inr assump_9 =>
        cases assump_7
        case intro assump_82 assump_83 =>
          apply Or.inl
          intro assump_88
          intro assump_89
          cases assump_89
          case inl assump_90 =>
            have assump_118 : (False → False) := by
              intro assump_97
              apply False.elim assump_97
            let assump_96 := assump_88 assump_118
            apply False.elim assump_96
          case inr assump_91 =>
            have assump_119 : (False → False) := by
              intro assump_108
              apply False.elim assump_108
            let assump_107 := assump_88 assump_119
            apply False.elim assump_107


variable (p1 p4 p3 : Prop)
theorem file36_124261 : (((((False ∨ p3) ∨ (p1 → p4)) → ((p3 ∧ False) → False)) → False) → False) := by
  intro assump_1
  have assump_16 : (((False ∨ p3) ∨ (p1 → p4)) → ((p3 ∧ False) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_8
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p2 p1 p3 p5 p0 p7 : Prop)
theorem file36_124687 : (((((p0 → False) ∧ (True ∨ p2)) → ((True ∨ p7) ∨ (False ∧ p0))) → (((p3 → p2) ∧ (p1 ∧ False)) → False)) → ((((p2 ∨ True) ∧ (p5 → False)) → ((p2 → True) ∧ (p5 → False))) ∨ (((p2 → False) ∨ (p2 → False)) ∧ ((False → False) ∨ (False ∨ False))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  apply And.intro
  intro assump_5
  apply True.intro
  intro assump_6
  cases assump_4
  case intro assump_9 assump_10 =>
    cases assump_9
    case inl assump_11 =>
      have assump_29 : p5 := by
        exact assump_6
      let assump_17 := assump_10 assump_29
      apply False.elim assump_17
    case inr assump_12 =>
      have assump_30 : p5 := by
        exact assump_6
      let assump_25 := assump_10 assump_30
      apply False.elim assump_25


variable (p2 p6 p3 p4 p1 p5 p7 : Prop)
theorem file36_125504 : (((((p2 ∧ p5) ∨ (True ∨ p1)) ∨ ((p3 ∨ p3) → (p6 ∨ p2))) → False) → ((((p1 → False) ∧ (p7 → False)) ∧ ((p3 ∨ p1) ∧ (p5 → p2))) → (((p7 ∧ False) ∨ (p6 ∨ p2)) ∨ ((True → p4) ∧ (p3 ∧ p3))))) := by
  intro assump_36
  intro assump_37
  cases assump_37
  case intro assump_38 assump_39 =>
    cases assump_38
    case intro assump_40 assump_41 =>
      cases assump_39
      case intro assump_46 assump_47 =>
        cases assump_46
        case inl assump_48 =>
          apply Or.inr
          apply And.intro
          intro assump_56
          have assump_80 : (((p2 ∧ p5) ∨ (True ∨ p1)) ∨ ((p3 ∨ p3) → (p6 ∨ p2))) := by
            apply Or.inl
            apply Or.inr
            apply Or.inl
            apply True.intro
          let assump_59 := assump_36 assump_80
          apply False.elim assump_59
          apply And.intro
          exact assump_48
          exact assump_48
        case inr assump_49 =>
          have assump_81 : (((p2 ∧ p5) ∨ (True ∨ p1)) ∨ ((p3 ∨ p3) → (p6 ∨ p2))) := by
            apply Or.inl
            apply Or.inr
            apply Or.inl
            apply True.intro
          let assump_76 := assump_36 assump_81
          apply False.elim assump_76


variable (p2 p3 p5 p1 p7 p6 p4 p0 : Prop)
theorem file36_126760 : (((((p4 → p5) ∧ (p7 ∨ p1)) → ((p6 ∧ p1) → (p3 → p3))) → (((False ∨ p5) ∧ (p1 → False)) ∨ ((p4 → False) ∨ (p6 ∨ p6)))) → ((((False ∨ p2) → False) → False) → (((p3 ∨ p3) → False) → ((p2 ∨ p0) ∨ (False → p3))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  apply Or.inr
  intro assump_10
  apply False.elim assump_10


variable (p6 p7 p5 p1 p2 p3 : Prop)
theorem file36_127148 : ((((((p5 ∧ p7) → (False ∨ p1)) → False) → False) ∧ ((((p2 ∨ p2) → False) → ((p6 ∨ True) ∨ (p5 ∨ p6))) ∧ (((p3 ∧ p5) → (p6 → p5)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_26 : ((p3 ∧ p5) → (p6 → p5)) := by
        intro assump_13
        intro assump_14
        cases assump_13
        case intro assump_17 assump_18 =>
          exact assump_18
      let assump_12 := assump_7 assump_26
      apply False.elim assump_12


variable (p4 p6 p7 p3 : Prop)
theorem file36_127748 : ((((((p3 → False) → (True ∨ False)) → False) → (((False ∧ p6) → False) ∨ ((p4 ∨ p7) ∧ (False ∨ False)))) → False) → False) := by
  intro assump_1
  have assump_16 : ((((p3 → False) → (True ∨ False)) → False) → (((False ∧ p6) → False) ∨ ((p4 ∨ p7) ∧ (False ∨ False)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      apply False.elim assump_9
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p3 p5 p2 p0 : Prop)
theorem file36_128284 : ((((((True ∧ p3) → (p3 → False)) → ((p3 ∧ False) → (p5 ∧ False))) ∨ (((p0 ∧ p0) ∨ (p5 ∧ p2)) ∧ ((False → False) ∨ (p5 ∧ False)))) → False) → False) := by
  intro assump_1
  have assump_22 : ((((True ∧ p3) → (p3 → False)) → ((p3 ∧ False) → (p5 ∧ False))) ∨ (((p0 ∧ p0) ∨ (p5 ∧ p2)) ∧ ((False → False) ∨ (p5 ∧ False)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    apply And.intro
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_8
    cases assump_6
    case intro assump_13 assump_14 =>
      apply False.elim assump_14
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p1 p2 : Prop)
theorem file36_128973 : (((((p1 ∨ p2) ∧ (False → False)) ∨ ((p1 → False) ∨ (p2 → False))) → False) → False) := by
  intro assump_1
  have assump_19 : (((p1 ∨ p2) ∧ (False → False)) ∨ ((p1 → False) ∨ (p2 → False))) := by
    apply Or.inr
    apply Or.inl
    intro assump_5
    have assump_20 : (((p1 ∨ p2) ∧ (False → False)) ∨ ((p1 → False) ∨ (p2 → False))) := by
      apply Or.inl
      apply And.intro
      apply Or.inl
      exact assump_5
      intro assump_10
      apply False.elim assump_10
    let assump_9 := assump_1 assump_20
    apply False.elim assump_9
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p2 p1 p5 p7 p4 : Prop)
theorem file36_129640 : (((((p4 → False) ∨ (p5 ∧ p5)) ∧ ((p7 → p2) ∧ (p5 → False))) ∧ (((p5 → p2) → (p1 → True)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_5
        case intro assump_10 assump_11 =>
          have assump_44 : ((p5 → p2) → (p1 → True)) := by
            intro assump_19
            intro assump_20
            apply True.intro
          let assump_18 := assump_3 assump_44
          apply False.elim assump_18
      case inr assump_7 =>
        cases assump_7
        case intro assump_24 assump_25 =>
          cases assump_5
          case intro assump_30 assump_31 =>
            have assump_45 : ((p5 → p2) → (p1 → True)) := by
              intro assump_39
              intro assump_40
              apply True.intro
            let assump_38 := assump_3 assump_45
            apply False.elim assump_38


variable (p6 p1 p5 p0 p4 p7 p2 : Prop)
theorem file36_130680 : (((((p7 ∨ False) → False) ∧ ((p1 → p1) → False)) → (((True ∧ p2) ∧ (p1 → p4)) → ((False ∧ p1) → (p0 ∨ p5)))) ∧ ((((p6 → True) → False) → ((p1 ∧ True) ∨ (p7 → False))) ∨ (((p2 ∨ False) → (p4 ∧ p7)) → ((p0 → False) → False)))) := by
  apply And.intro
  intro assump_23
  intro assump_24
  intro assump_25
  cases assump_25
  case intro assump_26 assump_27 =>
    apply False.elim assump_26
  apply Or.inl
  intro assump_30
  apply Or.inr
  intro assump_33
  have assump_42 : (p6 → True) := by
    intro assump_38
    apply True.intro
  let assump_37 := assump_30 assump_42
  apply False.elim assump_37


variable (p4 p5 : Prop)
theorem file36_131328 : (((((False ∧ p4) → False) ∧ ((p4 ∨ p4) ∨ (False → p5))) → False) → False) := by
  intro assump_1
  have assump_16 : (((False ∧ p4) → False) ∧ ((p4 ∨ p4) ∨ (False → p5))) := by
    apply And.intro
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
    apply Or.inr
    intro assump_10
    apply False.elim assump_10
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p1 p5 p3 p7 p4 p6 : Prop)
theorem file36_131823 : (((((p3 ∨ p4) → (p6 ∧ p1)) ∨ ((p4 → p3) ∨ (True → False))) ∧ (((p7 → False) ∧ (p3 ∧ True)) ∧ ((False → p7) ∧ (True ∧ p1)))) → ((((p7 ∨ p4) → (True → False)) ∨ ((p4 → False) ∨ (p6 ∧ True))) → (((p3 → p5) ∧ (False ∨ False)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_5
    case inl assump_8 =>
      apply False.elim assump_8
    case inr assump_9 =>
      apply False.elim assump_9


variable (p0 p2 p4 p7 p3 : Prop)
theorem file36_132354 : ((((((p0 → p3) ∧ (p7 ∧ False)) → ((p4 ∧ p4) ∧ (p0 ∨ p7))) ∧ (((p4 ∧ p7) → False) ∨ ((True → False) → False))) ∧ ((((p2 → False) ∨ (p4 ∧ p3)) ∨ ((p7 → False) ∧ (False ∧ p7))) ∧ (((False ∧ True) → False) → False))) → False) := by
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
          case inl assump_14 =>
            cases assump_14
            case inl assump_16 =>
              have assump_102 : ((False ∧ True) → False) := by
                intro assump_23
                cases assump_23
                case intro assump_24 assump_25 =>
                  apply False.elim assump_24
              let assump_22 := assump_13 assump_102
              apply False.elim assump_22
            case inr assump_17 =>
              cases assump_17
              case intro assump_31 assump_32 =>
                have assump_103 : ((False ∧ True) → False) := by
                  intro assump_40
                  cases assump_40
                  case intro assump_41 assump_42 =>
                    apply False.elim assump_41
                let assump_39 := assump_13 assump_103
                apply False.elim assump_39
          case inr assump_15 =>
            cases assump_15
            case intro assump_48 assump_49 =>
              cases assump_49
              case intro assump_52 assump_53 =>
                apply False.elim assump_52
      case inr assump_9 =>
        cases assump_3
        case intro assump_58 assump_59 =>
          cases assump_58
          case inl assump_60 =>
            cases assump_60
            case inl assump_62 =>
              have assump_104 : ((False ∧ True) → False) := by
                intro assump_69
                cases assump_69
                case intro assump_70 assump_71 =>
                  apply False.elim assump_70
              let assump_68 := assump_59 assump_104
              apply False.elim assump_68
            case inr assump_63 =>
              cases assump_63
              case intro assump_77 assump_78 =>
                have assump_105 : ((False ∧ True) → False) := by
                  intro assump_86
                  cases assump_86
                  case intro assump_87 assump_88 =>
                    apply False.elim assump_87
                let assump_85 := assump_59 assump_105
                apply False.elim assump_85
          case inr assump_61 =>
            cases assump_61
            case intro assump_94 assump_95 =>
              cases assump_95
              case intro assump_98 assump_99 =>
                apply False.elim assump_98


variable (p5 p3 p2 p0 p4 : Prop)
theorem file36_135173 : ((((((p5 ∨ p2) → False) ∨ ((p0 ∧ p4) ∧ (p4 → False))) → (((p3 → True) ∧ (True ∧ p2)) → False)) → False) → False) := by
  intro assump_1
  have assump_42 : ((((p5 ∨ p2) → False) ∨ ((p0 ∧ p4) ∧ (p4 → False))) → (((p3 → True) ∧ (True ∧ p2)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        cases assump_5
        case inl assump_17 =>
          have assump_43 : (p5 ∨ p2) := by
            apply Or.inr
            exact assump_12
          let assump_21 := assump_17 assump_43
          apply False.elim assump_21
        case inr assump_18 =>
          cases assump_18
          case intro assump_25 assump_26 =>
            cases assump_25
            case intro assump_27 assump_28 =>
              have assump_44 : p4 := by
                exact assump_28
              let assump_35 := assump_26 assump_44
              apply False.elim assump_35
  let assump_4 := assump_1 assump_42
  apply False.elim assump_4


variable (p1 p7 p4 p3 p6 : Prop)
theorem file36_136274 : (((((p1 → False) → (True ∧ True)) → False) ∧ (((p1 ∧ p3) → (p7 ∨ p7)) ∧ ((p7 ∧ p6) → (p4 → p6)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_19 : ((p1 → False) → (True ∧ True)) := by
        intro assump_15
        apply And.intro
        apply True.intro
        apply True.intro
      let assump_14 := assump_2 assump_19
      apply False.elim assump_14


variable (p6 p4 : Prop)
theorem file36_136791 : (((((p4 ∧ False) ∧ (p6 ∨ p4)) → False) → False) → False) := by
  intro assump_1
  have assump_17 : (((p4 ∧ False) ∧ (p6 ∨ p4)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_9
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


