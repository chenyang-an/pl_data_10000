variable (p6 p0 p5 p1 p7 p2 : Prop)
theorem file92_44 : (((((True ∧ p0) ∧ (p6 ∨ p5)) ∧ ((p5 → p2) ∧ (p2 ∧ p7))) ∧ (((p2 → p6) → (p1 ∨ p2)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_7
          case inl assump_14 =>
            cases assump_5
            case intro assump_18 assump_19 =>
              cases assump_19
              case intro assump_22 assump_23 =>
                have assump_58 : ((p2 → p6) → (p1 ∨ p2)) := by
                  intro assump_31
                  apply Or.inr
                  exact assump_22
                let assump_30 := assump_3 assump_58
                apply False.elim assump_30
          case inr assump_15 =>
            cases assump_5
            case intro assump_39 assump_40 =>
              cases assump_40
              case intro assump_43 assump_44 =>
                have assump_59 : ((p2 → p6) → (p1 ∨ p2)) := by
                  intro assump_52
                  apply Or.inr
                  exact assump_43
                let assump_51 := assump_3 assump_59
                apply False.elim assump_51


variable (p3 p7 p4 p1 p5 p6 p0 : Prop)
theorem file92_1365 : (((((p4 ∨ p1) ∧ (True ∧ p7)) ∨ ((p5 → p4) → (p1 ∨ True))) → (((p0 ∧ False) → (p1 ∧ p3)) ∨ ((True → p3) ∧ (p7 ∧ p0)))) ∧ ((((p0 → True) ∨ (p7 → False)) → False) → (((p6 → False) ∧ (p3 → p7)) ∧ ((p0 ∧ True) → False)))) := by
  apply And.intro
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_5
        case intro assump_10 assump_11 =>
          apply Or.inl
          intro assump_16
          apply And.intro
          cases assump_16
          case intro assump_17 assump_18 =>
            apply False.elim assump_18
          cases assump_16
          case intro assump_23 assump_24 =>
            apply False.elim assump_24
      case inr assump_7 =>
        cases assump_5
        case intro assump_31 assump_32 =>
          apply Or.inl
          intro assump_37
          apply And.intro
          cases assump_37
          case intro assump_38 assump_39 =>
            apply False.elim assump_39
          cases assump_37
          case intro assump_44 assump_45 =>
            apply False.elim assump_45
  case inr assump_3 =>
    apply Or.inl
    intro assump_52
    apply And.intro
    cases assump_52
    case intro assump_53 assump_54 =>
      apply False.elim assump_54
    cases assump_52
    case intro assump_59 assump_60 =>
      apply False.elim assump_60
  intro assump_65
  apply And.intro
  apply And.intro
  intro assump_66
  have assump_100 : ((p0 → True) ∨ (p7 → False)) := by
    apply Or.inl
    intro assump_72
    apply True.intro
  let assump_71 := assump_65 assump_100
  apply False.elim assump_71
  intro assump_76
  have assump_101 : ((p0 → True) ∨ (p7 → False)) := by
    apply Or.inl
    intro assump_82
    apply True.intro
  let assump_81 := assump_65 assump_101
  apply False.elim assump_81
  intro assump_86
  cases assump_86
  case intro assump_87 assump_88 =>
    have assump_102 : ((p0 → True) ∨ (p7 → False)) := by
      apply Or.inl
      intro assump_96
      apply True.intro
    let assump_95 := assump_65 assump_102
    apply False.elim assump_95


variable (p0 p2 p1 p7 p3 p4 p5 : Prop)
theorem file92_3554 : (((((False → p0) ∨ (True → False)) → ((True → p7) → False)) ∨ (((p5 → p5) → False) ∧ ((p5 → p4) ∧ (p5 ∨ p5)))) → ((((False → False) ∨ (p0 → False)) ∨ ((True ∨ p5) ∧ (p1 → False))) ∨ (((p2 → p3) ∨ (False ∧ p3)) ∧ ((p7 → False) → (p2 → p2))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply Or.inl
    apply Or.inl
    intro assump_6
    apply False.elim assump_6
  case inr assump_3 =>
    cases assump_3
    case intro assump_9 assump_10 =>
      cases assump_10
      case intro assump_13 assump_14 =>
        cases assump_14
        case inl assump_17 =>
          apply Or.inl
          apply Or.inl
          apply Or.inl
          intro assump_21
          apply False.elim assump_21
        case inr assump_18 =>
          apply Or.inl
          apply Or.inl
          apply Or.inl
          intro assump_26
          apply False.elim assump_26


variable (p4 p7 p3 p1 p5 : Prop)
theorem file92_4505 : ((((((True ∨ p1) → (p7 → False)) → False) ∧ (((p3 → False) → False) → ((p5 → False) → False))) ∧ ((((p4 → False) ∧ (True → False)) → False) → False)) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      have assump_31 : (((p4 → False) ∧ (True → False)) → False) := by
        intro assump_17
        cases assump_17
        case intro assump_18 assump_19 =>
          have assump_32 : True := by
            apply True.intro
          let assump_24 := assump_19 assump_32
          apply False.elim assump_24
      let assump_16 := assump_7 assump_31
      apply False.elim assump_16


variable (p6 p2 p3 p4 p5 p0 : Prop)
theorem file92_5240 : ((((((p4 ∨ p0) ∨ (p3 ∧ p5)) → ((p2 ∧ p3) ∨ (False → p4))) ∨ (((p3 ∨ p6) → False) ∨ ((True → False) → False))) → False) → False) := by
  intro assump_7
  have assump_38 : ((((p4 ∨ p0) ∨ (p3 ∧ p5)) → ((p2 ∧ p3) ∨ (False → p4))) ∨ (((p3 ∨ p6) → False) ∨ ((True → False) → False))) := by
    apply Or.inl
    intro assump_11
    cases assump_11
    case inl assump_12 =>
      cases assump_12
      case inl assump_14 =>
        apply Or.inr
        intro assump_18
        apply False.elim assump_18
      case inr assump_15 =>
        apply Or.inr
        intro assump_23
        apply False.elim assump_23
    case inr assump_13 =>
      cases assump_13
      case intro assump_26 assump_27 =>
        apply Or.inr
        intro assump_32
        apply False.elim assump_32
  let assump_10 := assump_7 assump_38
  apply False.elim assump_10


variable (p5 p1 p2 p0 p4 p7 p3 p6 : Prop)
theorem file92_6146 : ((((((p7 → p5) → False) ∧ ((p4 → False) ∧ (p1 → False))) ∨ (((p2 ∨ p4) ∧ (p1 ∧ True)) ∧ ((p3 → p0) ∨ (p0 → False)))) ∧ ((((p6 ∧ False) → False) ∧ ((p5 ∧ p0) ∧ (p1 ∧ False))) ∧ (((False ∧ p0) → False) ∨ ((False ∧ p2) ∧ (p0 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          cases assump_3
          case intro assump_16 assump_17 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              cases assump_19
              case intro assump_22 assump_23 =>
                cases assump_22
                case intro assump_24 assump_25 =>
                  cases assump_23
                  case intro assump_30 assump_31 =>
                    apply False.elim assump_31
    case inr assump_5 =>
      cases assump_5
      case intro assump_36 assump_37 =>
        cases assump_36
        case intro assump_38 assump_39 =>
          cases assump_38
          case inl assump_40 =>
            cases assump_39
            case intro assump_44 assump_45 =>
              cases assump_37
              case inl assump_50 =>
                cases assump_3
                case intro assump_54 assump_55 =>
                  cases assump_54
                  case intro assump_56 assump_57 =>
                    cases assump_57
                    case intro assump_60 assump_61 =>
                      cases assump_60
                      case intro assump_62 assump_63 =>
                        cases assump_61
                        case intro assump_68 assump_69 =>
                          apply False.elim assump_69
              case inr assump_51 =>
                cases assump_3
                case intro assump_76 assump_77 =>
                  cases assump_76
                  case intro assump_78 assump_79 =>
                    cases assump_79
                    case intro assump_82 assump_83 =>
                      cases assump_82
                      case intro assump_84 assump_85 =>
                        cases assump_83
                        case intro assump_90 assump_91 =>
                          apply False.elim assump_91
          case inr assump_41 =>
            cases assump_39
            case intro assump_98 assump_99 =>
              cases assump_37
              case inl assump_104 =>
                cases assump_3
                case intro assump_108 assump_109 =>
                  cases assump_108
                  case intro assump_110 assump_111 =>
                    cases assump_111
                    case intro assump_114 assump_115 =>
                      cases assump_114
                      case intro assump_116 assump_117 =>
                        cases assump_115
                        case intro assump_122 assump_123 =>
                          apply False.elim assump_123
              case inr assump_105 =>
                cases assump_3
                case intro assump_130 assump_131 =>
                  cases assump_130
                  case intro assump_132 assump_133 =>
                    cases assump_133
                    case intro assump_136 assump_137 =>
                      cases assump_136
                      case intro assump_138 assump_139 =>
                        cases assump_137
                        case intro assump_144 assump_145 =>
                          apply False.elim assump_145


variable (p2 p1 p6 p5 p3 p7 p4 p0 : Prop)
theorem file92_9768 : (((((False ∧ p3) ∨ (p6 ∧ p5)) ∧ ((True → False) → False)) ∧ (((False → p0) → False) → False)) ∨ ((((True ∨ p7) → False) → ((p1 → False) → (p3 ∨ p7))) ∨ (((True → False) ∨ (p0 → p5)) ∧ ((p2 → False) → (p5 ∧ p4))))) := by
  apply Or.inr
  apply Or.inl
  intro assump_1
  intro assump_2
  have assump_11 : (True ∨ p7) := by
    apply Or.inl
    apply True.intro
  let assump_7 := assump_1 assump_11
  apply False.elim assump_7


variable (p7 p1 p4 p6 p5 p2 : Prop)
theorem file92_10252 : ((((((p1 → p4) → False) → ((p6 → True) ∨ (p1 ∧ p4))) ∨ (((p7 ∨ p1) ∨ (p2 → False)) ∨ ((p5 ∧ p4) ∧ (False → False)))) → False) → False) := by
  intro assump_1
  have assump_12 : ((((p1 → p4) → False) → ((p6 → True) ∨ (p1 ∧ p4))) ∨ (((p7 ∨ p1) ∨ (p2 → False)) ∨ ((p5 ∧ p4) ∧ (False → False)))) := by
    apply Or.inl
    intro assump_5
    apply Or.inl
    intro assump_8
    apply True.intro
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p2 p1 p0 p4 p6 p3 p7 : Prop)
theorem file92_10771 : ((((((False → True) → False) → False) → (((False ∨ p1) ∧ (p7 ∨ p0)) → ((p6 ∨ p3) ∨ (True → False)))) ∧ ((((p0 → p2) ∧ (p2 ∨ True)) → ((False → False) ∨ (p4 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_29 : (((p0 → p2) ∧ (p2 ∨ True)) → ((False → False) ∨ (p4 → False))) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        cases assump_11
        case inl assump_14 =>
          apply Or.inl
          intro assump_18
          apply False.elim assump_18
        case inr assump_15 =>
          apply Or.inl
          intro assump_23
          apply False.elim assump_23
    let assump_8 := assump_3 assump_29
    apply False.elim assump_8


variable (p2 p7 p1 p0 p3 p4 p6 : Prop)
theorem file92_11591 : ((((((p6 → p6) ∨ (p3 ∨ p2)) ∨ ((p7 ∧ p4) → (p0 → False))) ∨ (((p1 ∨ False) ∨ (p2 ∧ p4)) → ((p2 → p1) ∨ (True ∨ p4)))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p6 → p6) ∨ (p3 ∨ p2)) ∨ ((p7 ∧ p4) → (p0 → False))) ∨ (((p1 ∨ False) ∨ (p2 ∧ p4)) → ((p2 → p1) ∨ (True ∨ p4)))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    intro assump_5
    exact assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p2 p1 p5 p3 p4 : Prop)
theorem file92_12102 : (((((p5 → False) → False) ∧ ((p1 → False) → (p2 → p4))) ∧ (((p2 ∧ False) ∧ (p2 ∨ p1)) ∧ ((p4 ∨ p3) ∨ (p2 → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            apply False.elim assump_15


variable (p2 p3 p4 p7 p5 p0 p6 : Prop)
theorem file92_12656 : ((((((p0 → False) ∨ (p5 → False)) ∨ ((p6 → p4) → False)) → (((p0 → False) ∧ (p7 ∨ p0)) ∧ ((p7 ∧ True) → False))) ∧ ((((p2 → p2) → (p7 → False)) → ((p3 → p3) ∨ (True → p2))) ∧ (((False → False) → False) ∧ ((p0 ∨ p2) ∨ (p0 ∧ True))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_11
        case inl assump_14 =>
          cases assump_14
          case inl assump_16 =>
            have assump_52 : (False → False) := by
              intro assump_22
              apply False.elim assump_22
            let assump_21 := assump_10 assump_52
            apply False.elim assump_21
          case inr assump_17 =>
            have assump_53 : (False → False) := by
              intro assump_32
              apply False.elim assump_32
            let assump_31 := assump_10 assump_53
            apply False.elim assump_31
        case inr assump_15 =>
          cases assump_15
          case intro assump_38 assump_39 =>
            have assump_54 : (False → False) := by
              intro assump_46
              apply False.elim assump_46
            let assump_45 := assump_10 assump_54
            apply False.elim assump_45


variable (p6 p7 p1 p4 : Prop)
theorem file92_14016 : (((((p1 → True) ∧ (p7 → p4)) ∧ ((True ∧ True) → False)) → False) ∨ ((((False → False) → (False → p6)) → False) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_16 : (True ∧ True) := by
        apply And.intro
        apply True.intro
        apply True.intro
      let assump_12 := assump_3 assump_16
      apply False.elim assump_12


variable (p0 p5 p1 p6 p2 p7 : Prop)
theorem file92_14533 : (((((p1 ∧ p6) ∨ (True → False)) → ((p7 → False) ∨ (p5 → p7))) → (((p1 ∨ True) ∨ (True ∧ p2)) ∨ ((p0 ∨ p2) → False))) ∨ ((((p6 → p7) → False) ∧ ((p0 → False) → False)) → (((True ∧ True) → False) → False))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply Or.inr
  apply True.intro


theorem file92_14864 : (((((True ∨ False) → False) → False) → False) → False) := by
  intro assump_1
  have assump_15 : (((True ∨ False) → False) → False) := by
    intro assump_5
    have assump_16 : (True ∨ False) := by
      apply Or.inl
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p4 p5 p0 p2 p1 p3 p7 p6 : Prop)
theorem file92_15305 : (((((p5 ∨ False) ∨ (True → False)) → False) → (((p3 ∨ p7) ∨ (True ∨ p3)) → False)) → ((((p2 ∨ p0) ∧ (p0 → False)) ∨ ((p4 ∨ p5) ∨ (p1 ∨ p0))) ∨ (((p4 → p4) ∨ (p3 ∧ True)) ∨ ((True ∨ p4) ∨ (p6 → False))))) := by
  intro assump_1
  apply Or.inr
  apply Or.inl
  apply Or.inl
  intro assump_4
  exact assump_4


variable (p6 p1 p7 p5 p3 : Prop)
theorem file92_15668 : (((((p6 ∨ p1) ∨ (p5 ∨ p7)) → False) ∧ (((True → False) ∨ (True → False)) ∧ ((False ∨ p5) ∧ (p3 → False)))) → False) := by
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
          case inl assump_14 =>
            apply False.elim assump_14
          case inr assump_15 =>
            have assump_46 : True := by
              apply True.intro
            let assump_24 := assump_8 assump_46
            apply False.elim assump_24
      case inr assump_9 =>
        cases assump_7
        case intro assump_30 assump_31 =>
          cases assump_30
          case inl assump_32 =>
            apply False.elim assump_32
          case inr assump_33 =>
            have assump_47 : True := by
              apply True.intro
            let assump_42 := assump_9 assump_47
            apply False.elim assump_42


variable (p1 p6 p4 p2 p3 p5 : Prop)
theorem file92_16752 : (((((True → False) → (p4 → p2)) ∧ ((True → False) ∧ (True → p1))) → False) ∨ ((((True → False) → False) → False) → (((p5 ∨ p6) → (False → p3)) ∧ ((p6 → False) → (p1 → p5))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_18 : True := by
        apply True.intro
      let assump_14 := assump_6 assump_18
      apply False.elim assump_14


variable (p1 p7 p2 p5 p3 : Prop)
theorem file92_17262 : ((((((p1 → False) ∧ (p7 → False)) ∨ ((p2 ∨ p3) → (p5 ∨ p7))) → (((False → p3) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_39 : ((((p1 → False) ∧ (p7 → False)) ∨ ((p2 ∨ p3) → (p5 ∨ p7))) → (((False → p3) → False) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case inl assump_9 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        have assump_40 : (False → p3) := by
          intro assump_20
          apply False.elim assump_20
        let assump_19 := assump_6 assump_40
        apply False.elim assump_19
    case inr assump_10 =>
      have assump_41 : (False → p3) := by
        intro assump_30
        apply False.elim assump_30
      let assump_29 := assump_6 assump_41
      apply False.elim assump_29
  let assump_4 := assump_1 assump_39
  apply False.elim assump_4


variable (p0 p3 p2 p4 p5 p7 : Prop)
theorem file92_18176 : (((((p2 ∧ p2) ∨ (False → False)) → ((False ∧ p7) ∧ (p3 → p7))) ∧ (((False ∨ p0) ∨ (p3 → False)) ∨ ((p4 ∨ p2) ∨ (p5 ∨ p2)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          apply False.elim assump_10
        case inr assump_11 =>
          have assump_86 : ((p2 ∧ p2) ∨ (False → False)) := by
            apply Or.inr
            intro assump_18
            apply False.elim assump_18
          let assump_17 := assump_2 assump_86
          let assump_21 := And.left assump_17
          let assump_22 := And.left assump_21
          apply False.elim assump_22
      case inr assump_9 =>
        have assump_87 : ((p2 ∧ p2) ∨ (False → False)) := by
          apply Or.inr
          intro assump_30
          apply False.elim assump_30
        let assump_29 := assump_2 assump_87
        let assump_33 := And.left assump_29
        let assump_34 := And.left assump_33
        apply False.elim assump_34
    case inr assump_7 =>
      cases assump_7
      case inl assump_38 =>
        cases assump_38
        case inl assump_40 =>
          have assump_88 : ((p2 ∧ p2) ∨ (False → False)) := by
            apply Or.inr
            intro assump_46
            apply False.elim assump_46
          let assump_45 := assump_2 assump_88
          let assump_49 := And.left assump_45
          let assump_50 := And.left assump_49
          apply False.elim assump_50
        case inr assump_41 =>
          have assump_89 : ((p2 ∧ p2) ∨ (False → False)) := by
            apply Or.inl
            apply And.intro
            exact assump_41
            exact assump_41
          let assump_57 := assump_2 assump_89
          let assump_58 := And.left assump_57
          let assump_59 := And.left assump_58
          apply False.elim assump_59
      case inr assump_39 =>
        cases assump_39
        case inl assump_63 =>
          have assump_90 : ((p2 ∧ p2) ∨ (False → False)) := by
            apply Or.inr
            intro assump_69
            apply False.elim assump_69
          let assump_68 := assump_2 assump_90
          let assump_72 := And.left assump_68
          let assump_73 := And.left assump_72
          apply False.elim assump_73
        case inr assump_64 =>
          have assump_91 : ((p2 ∧ p2) ∨ (False → False)) := by
            apply Or.inl
            apply And.intro
            exact assump_64
            exact assump_64
          let assump_80 := assump_2 assump_91
          let assump_81 := And.left assump_80
          let assump_82 := And.left assump_81
          apply False.elim assump_82


variable (p7 p0 p2 p5 p6 : Prop)
theorem file92_20947 : ((((((False ∧ False) → (p7 → False)) ∨ ((p6 → p0) → False)) ∧ (((p2 → False) ∧ (False ∧ p5)) → False)) → False) → False) := by
  intro assump_27
  have assump_51 : ((((False ∧ False) → (p7 → False)) ∨ ((p6 → p0) → False)) ∧ (((p2 → False) ∧ (False ∧ p5)) → False)) := by
    apply And.intro
    apply Or.inl
    intro assump_31
    intro assump_32
    cases assump_31
    case intro assump_35 assump_36 =>
      apply False.elim assump_35
    intro assump_39
    cases assump_39
    case intro assump_40 assump_41 =>
      cases assump_41
      case intro assump_44 assump_45 =>
        apply False.elim assump_44
  let assump_30 := assump_27 assump_51
  apply False.elim assump_30


variable (p5 p2 p0 p7 p6 p1 p4 : Prop)
theorem file92_21692 : (((((False → p1) ∧ (p7 ∧ p4)) ∨ ((p6 ∧ False) → (p2 → False))) ∨ (((p5 → True) → False) ∨ ((p4 ∧ p7) → (p5 ∨ p5)))) ∨ ((((p7 ∨ p2) ∨ (p6 ∨ p2)) → False) ∨ (((p1 ∧ p6) ∧ (p7 ∧ p0)) ∨ ((p6 → p0) ∧ (p7 → p2))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inr
  intro assump_4
  intro assump_5
  cases assump_4
  case intro assump_8 assump_9 =>
    apply False.elim assump_9


variable (p0 p5 p3 : Prop)
theorem file92_22118 : ((((((True ∧ p5) → False) ∧ ((p0 ∨ False) ∧ (p3 ∧ False))) → False) → False) → False) := by
  intro assump_1
  have assump_27 : ((((True ∧ p5) → False) ∧ ((p0 ∨ False) ∧ (p3 ∧ False))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          cases assump_11
          case intro assump_16 assump_17 =>
            apply False.elim assump_17
        case inr assump_13 =>
          apply False.elim assump_13
  let assump_4 := assump_1 assump_27
  apply False.elim assump_4


variable (p6 p2 p7 p5 p4 : Prop)
theorem file92_22805 : ((((((p5 ∧ p5) ∧ (p4 ∨ p2)) → ((p6 ∧ False) → False)) → False) ∧ ((((p7 ∧ p6) ∧ (p5 ∨ p6)) → False) ∨ (((False ∨ True) ∨ (p7 → False)) → ((p2 ∧ False) → False)))) → False) := by
  intro assump_24
  cases assump_24
  case intro assump_25 assump_26 =>
    cases assump_26
    case inl assump_29 =>
      have assump_62 : (((p5 ∧ p5) ∧ (p4 ∨ p2)) → ((p6 ∧ False) → False)) := by
        intro assump_35
        intro assump_36
        cases assump_36
        case intro assump_37 assump_38 =>
          apply False.elim assump_38
      let assump_34 := assump_25 assump_62
      apply False.elim assump_34
    case inr assump_30 =>
      have assump_63 : (((p5 ∧ p5) ∧ (p4 ∨ p2)) → ((p6 ∧ False) → False)) := by
        intro assump_51
        intro assump_52
        cases assump_52
        case intro assump_53 assump_54 =>
          apply False.elim assump_54
      let assump_50 := assump_25 assump_63
      apply False.elim assump_50


variable (p3 p2 p4 p6 p1 p0 : Prop)
theorem file92_23801 : ((((((True ∧ p1) → (p4 → False)) → False) → (((False → True) ∨ (False ∧ p3)) → ((p3 ∨ p6) → False))) ∧ ((((True → p0) → (p2 → p2)) ∧ ((False → False) → False)) ∧ (((p4 ∨ p2) ∨ (False → False)) → ((True ∨ False) → (p0 → p1))))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_7
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        have assump_33 : (False → False) := by
          intro assump_27
          apply False.elim assump_27
        let assump_26 := assump_13 assump_33
        apply False.elim assump_26


variable (p6 p4 p2 p1 p3 p7 : Prop)
theorem file92_24480 : (((((False → p3) → (p3 ∨ p1)) ∧ ((p2 ∧ p7) → (p4 ∨ p6))) ∧ (((p3 ∧ p2) ∧ (p2 ∧ False)) ∧ ((False → False) → (p6 → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_13
            case intro assump_20 assump_21 =>
              apply False.elim assump_21


variable (p4 p5 p1 p6 p2 p0 : Prop)
theorem file92_25114 : ((((((True ∧ False) ∧ (p5 ∨ False)) → ((p1 ∨ p5) ∧ (p0 → False))) ∨ (((p6 ∨ p4) → False) → ((p2 ∨ p5) → (p5 → False)))) → False) → False) := by
  intro assump_1
  have assump_28 : ((((True ∧ False) ∧ (p5 ∨ False)) → ((p1 ∨ p5) ∧ (p0 → False))) ∨ (((p6 ∨ p4) → False) → ((p2 ∨ p5) → (p5 → False)))) := by
    apply Or.inl
    intro assump_5
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_9
    intro assump_14
    cases assump_5
    case intro assump_17 assump_18 =>
      cases assump_17
      case intro assump_19 assump_20 =>
        apply False.elim assump_20
  let assump_4 := assump_1 assump_28
  apply False.elim assump_4


variable (p1 p4 p0 p5 p6 p2 p7 p3 : Prop)
theorem file92_25927 : (((((p4 ∨ p5) ∨ (p1 ∧ False)) ∧ ((p6 ∧ p7) ∨ (p0 → False))) ∨ (((p2 → False) ∧ (p6 ∧ p2)) → ((p0 ∨ False) ∧ (p6 ∨ p0)))) ∨ ((((p6 → False) ∧ (p6 → p3)) → False) → (((p1 → p5) → False) ∧ ((p4 → False) ∨ (p4 → p4))))) := by
  apply Or.inl
  apply Or.inr
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_28 : p2 := by
        exact assump_7
      let assump_14 := assump_2 assump_28
      apply False.elim assump_14
  cases assump_1
  case intro assump_18 assump_19 =>
    cases assump_19
    case intro assump_22 assump_23 =>
      apply Or.inl
      exact assump_22


variable (p5 p0 p4 p6 : Prop)
theorem file92_26656 : (((((False → p5) ∧ (p0 → False)) ∧ ((False → False) → False)) → (((p6 ∨ p4) ∧ (p5 → False)) → False)) ∨ ((((False → False) → (p0 ∧ p6)) → False) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_1
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          have assump_49 : (False → False) := by
            intro assump_22
            apply False.elim assump_22
          let assump_21 := assump_12 assump_49
          apply False.elim assump_21
    case inr assump_6 =>
      cases assump_1
      case intro assump_32 assump_33 =>
        cases assump_32
        case intro assump_34 assump_35 =>
          have assump_50 : (False → False) := by
            intro assump_43
            apply False.elim assump_43
          let assump_42 := assump_33 assump_50
          apply False.elim assump_42


variable (p3 p6 p7 p4 : Prop)
theorem file92_27694 : (((((p6 ∧ p4) ∨ (False → p7)) → False) → False) ∨ ((((p4 ∨ True) ∧ (p7 ∧ False)) → ((p3 ∧ p6) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  have assump_11 : ((p6 ∧ p4) ∨ (False → p7)) := by
    apply Or.inr
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p4 p6 p1 p2 p5 p0 p7 : Prop)
theorem file92_28092 : (((((False ∧ True) ∧ (p4 → False)) → ((p6 → p6) → False)) ∨ (((True ∧ p6) → (p6 → False)) ∨ ((p0 ∧ p6) → False))) ∨ ((((p6 ∧ p6) ∨ (p2 → p7)) → False) ∧ (((p2 → p2) ∧ (p1 → False)) ∨ ((p4 ∧ p1) ∧ (False ∨ p5))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      apply False.elim assump_7


variable (p4 p7 p6 p0 p2 : Prop)
theorem file92_28570 : (((((p2 ∨ p7) → False) → ((p0 ∧ False) → False)) ∨ (((p2 ∧ False) → (p2 → False)) → ((p6 ∧ p0) ∧ (p0 → p2)))) ∨ ((((p2 → False) ∧ (p4 → False)) ∧ ((p6 → False) ∧ (p6 ∧ p4))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    apply False.elim assump_4


variable (p4 p6 p3 p1 p0 p2 : Prop)
theorem file92_28965 : (((((p0 ∧ p0) → False) → ((p0 ∨ p0) → False)) ∨ (((p2 → p3) ∨ (p2 → p1)) → ((p3 → False) → False))) ∨ ((((p2 ∧ p6) → False) ∨ ((p3 ∧ p1) ∨ (p1 ∨ p4))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    have assump_21 : (p0 ∧ p0) := by
      apply And.intro
      exact assump_3
      exact assump_3
    let assump_9 := assump_1 assump_21
    apply False.elim assump_9
  case inr assump_4 =>
    have assump_22 : (p0 ∧ p0) := by
      apply And.intro
      exact assump_4
      exact assump_4
    let assump_17 := assump_1 assump_22
    apply False.elim assump_17


variable (p1 p7 p5 p0 p3 p6 p2 : Prop)
theorem file92_29664 : (((((True → False) → (p1 ∧ p7)) → False) → (((p6 → p3) → (True ∨ p2)) ∧ ((False ∨ p5) ∨ (True ∧ True)))) ∨ ((((p0 ∨ False) → False) → False) → False)) := by
  apply Or.inl
  intro assump_33
  apply And.intro
  intro assump_34
  apply Or.inl
  apply True.intro
  apply Or.inr
  apply And.intro
  apply True.intro
  apply True.intro


variable (p7 p5 p3 p1 p2 p4 p6 p0 : Prop)
theorem file92_30061 : ((((((True → p7) ∨ (p6 ∨ p2)) ∨ ((p4 → False) ∧ (p4 ∨ p2))) → (((p7 ∧ False) ∧ (True → False)) → ((p1 ∧ p4) ∨ (True → False)))) → ((((True ∨ p7) ∨ (p3 → False)) ∨ ((p2 → False) ∨ (p5 ∧ p0))) → False)) → False) := by
  intro assump_1
  have assump_19 : ((((True → p7) ∨ (p6 ∨ p2)) ∨ ((p4 → False) ∧ (p4 ∨ p2))) → (((p7 ∧ False) ∧ (True → False)) → ((p1 ∧ p4) ∨ (True → False)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        apply False.elim assump_10
  let assump_4 := assump_1 assump_19
  have assump_20 : (((True ∨ p7) ∨ (p3 → False)) ∨ ((p2 → False) ∨ (p5 ∧ p0))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_15 := assump_4 assump_20
  apply False.elim assump_15


variable (p2 p5 p7 p3 p0 p4 : Prop)
theorem file92_30954 : (((((False ∧ p7) ∧ (p0 ∧ False)) ∨ ((p5 ∨ p2) ∨ (p5 → p3))) → False) → ((((p7 → False) → False) → ((p7 → p3) ∧ (p4 ∨ p2))) → (((p2 ∨ False) ∨ (p7 → False)) ∧ ((p5 → False) ∨ (p2 ∨ p3))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  apply Or.inr
  intro assump_7
  have assump_36 : (((False ∧ p7) ∧ (p0 ∧ False)) ∨ ((p5 ∨ p2) ∨ (p5 → p3))) := by
    apply Or.inr
    apply Or.inr
    intro assump_12
    have assump_37 : (((False ∧ p7) ∧ (p0 ∧ False)) ∨ ((p5 ∨ p2) ∨ (p5 → p3))) := by
      apply Or.inr
      apply Or.inl
      apply Or.inl
      exact assump_12
    let assump_17 := assump_1 assump_37
    apply False.elim assump_17
  let assump_11 := assump_1 assump_36
  apply False.elim assump_11
  apply Or.inl
  intro assump_28
  have assump_38 : (((False ∧ p7) ∧ (p0 ∧ False)) ∨ ((p5 ∨ p2) ∨ (p5 → p3))) := by
    apply Or.inr
    apply Or.inl
    apply Or.inl
    exact assump_28
  let assump_32 := assump_1 assump_38
  apply False.elim assump_32


variable (p1 p0 p4 p7 p6 p3 : Prop)
theorem file92_31985 : (((((p3 → False) → False) → ((p0 → p0) ∨ (p6 ∧ p1))) → False) → ((((p7 → False) ∨ (True → p3)) → ((False → False) ∧ (True → p4))) ∧ (((True ∨ p6) ∧ (False → False)) ∨ ((False → False) ∧ (p1 → p3))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  apply And.intro
  intro assump_3
  apply False.elim assump_3
  intro assump_6
  cases assump_2
  case inl assump_9 =>
    have assump_44 : (((p3 → False) → False) → ((p0 → p0) ∨ (p6 ∧ p1))) := by
      intro assump_16
      apply Or.inl
      intro assump_19
      exact assump_19
    let assump_15 := assump_1 assump_44
    apply False.elim assump_15
  case inr assump_10 =>
    have assump_45 : (((p3 → False) → False) → ((p0 → p0) ∨ (p6 ∧ p1))) := by
      intro assump_30
      apply Or.inl
      intro assump_33
      exact assump_33
    let assump_29 := assump_1 assump_45
    apply False.elim assump_29
  apply Or.inl
  apply And.intro
  apply Or.inl
  apply True.intro
  intro assump_41
  apply False.elim assump_41


variable (p7 p5 p2 p3 p6 p1 : Prop)
theorem file92_33029 : ((((((p1 ∧ False) ∧ (p7 → False)) → ((p7 → False) ∨ (p2 → False))) ∨ (((p1 ∧ p7) → (p5 ∧ p5)) ∧ ((p6 ∧ False) → (p1 → p3)))) → False) → False) := by
  intro assump_1
  have assump_17 : ((((p1 ∧ False) ∧ (p7 → False)) → ((p7 → False) ∨ (p2 → False))) ∨ (((p1 ∧ p7) → (p5 ∧ p5)) ∧ ((p6 ∧ False) → (p1 → p3)))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_9
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p5 p2 p4 p1 p6 p7 p3 p0 : Prop)
theorem file92_33658 : (((((p2 ∧ p3) ∨ (p0 → False)) → ((True → False) → (p5 → False))) ∨ (((p3 ∧ p3) ∧ (p2 ∧ p3)) ∧ ((p7 → False) ∨ (p4 → False)))) ∨ ((((p1 → False) → False) ∨ ((p1 ∨ p4) ∧ (p6 ∨ p4))) → (((p2 ∧ False) ∨ (p1 ∧ p5)) ∨ ((p4 → False) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_6
  intro assump_7
  intro assump_8
  cases assump_6
  case inl assump_13 =>
    cases assump_13
    case intro assump_15 assump_16 =>
      have assump_34 : True := by
        apply True.intro
      let assump_23 := assump_7 assump_34
      apply False.elim assump_23
  case inr assump_14 =>
    have assump_35 : True := by
      apply True.intro
    let assump_30 := assump_7 assump_35
    apply False.elim assump_30


variable (p2 p7 p0 p5 p1 p4 p6 : Prop)
theorem file92_34429 : (((((p2 ∧ p6) ∨ (p7 → True)) ∨ ((p7 → False) → False)) → (((p7 ∨ True) ∧ (True → p4)) ∧ ((True → False) ∧ (p6 → p4)))) → ((((p0 → False) → False) ∧ ((p0 → False) ∧ (p2 → False))) → (((p7 → False) ∨ (p1 ∧ p5)) → ((p2 → False) → (True ∨ p1))))) := by
  intro assump_7
  intro assump_8
  intro assump_9
  intro assump_10
  cases assump_9
  case inl assump_13 =>
    cases assump_8
    case intro assump_17 assump_18 =>
      cases assump_18
      case intro assump_21 assump_22 =>
        apply Or.inl
        apply True.intro
  case inr assump_14 =>
    cases assump_14
    case intro assump_29 assump_30 =>
      cases assump_8
      case intro assump_35 assump_36 =>
        cases assump_36
        case intro assump_39 assump_40 =>
          apply Or.inl
          apply True.intro


variable (p3 p5 p1 p0 p4 : Prop)
theorem file92_35269 : ((((((True ∧ p4) → (p4 ∧ p3)) → ((True → False) → (p0 ∨ p0))) ∨ (((p5 → p0) ∨ (p1 → True)) → ((False ∧ p5) → False))) → False) → False) := by
  intro assump_1
  have assump_19 : ((((True ∧ p4) → (p4 ∧ p3)) → ((True → False) → (p0 ∨ p0))) ∨ (((p5 → p0) ∨ (p1 → True)) → ((False ∧ p5) → False))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    have assump_20 : True := by
      apply True.intro
    let assump_12 := assump_6 assump_20
    apply False.elim assump_12
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p3 p1 p7 p0 p5 : Prop)
theorem file92_35872 : (((((p0 ∨ p7) → False) → ((p1 → True) ∨ (True → False))) → False) → ((((p3 ∧ True) → (p0 → False)) ∧ ((p5 → False) → (p3 → p0))) ∧ (((p1 ∨ p1) → False) → ((p1 ∨ False) ∨ (p5 ∨ False))))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    have assump_51 : (((p0 ∨ p7) → False) → ((p1 → True) ∨ (True → False))) := by
      intro assump_15
      apply Or.inl
      intro assump_18
      apply True.intro
    let assump_14 := assump_1 assump_51
    apply False.elim assump_14
  intro assump_22
  intro assump_23
  have assump_52 : (((p0 ∨ p7) → False) → ((p1 → True) ∨ (True → False))) := by
    intro assump_31
    apply Or.inl
    intro assump_34
    apply True.intro
  let assump_30 := assump_1 assump_52
  apply False.elim assump_30
  intro assump_38
  have assump_53 : (((p0 ∨ p7) → False) → ((p1 → True) ∨ (True → False))) := by
    intro assump_44
    apply Or.inl
    intro assump_47
    apply True.intro
  let assump_43 := assump_1 assump_53
  apply False.elim assump_43


variable (p5 p1 p2 p3 p6 p4 : Prop)
theorem file92_37006 : ((((((p4 ∧ True) ∧ (p2 ∧ p4)) ∧ ((p6 → False) ∧ (False ∧ p5))) → (((False ∧ True) ∧ (p1 → False)) ∨ ((p3 → p2) → False))) → False) → False) := by
  intro assump_1
  have assump_33 : ((((p4 ∧ True) ∧ (p2 ∧ p4)) ∧ ((p6 → False) ∧ (False ∧ p5))) → (((False ∧ True) ∧ (p1 → False)) ∨ ((p3 → p2) → False))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_9
          case intro assump_16 assump_17 =>
            cases assump_7
            case intro assump_22 assump_23 =>
              cases assump_23
              case intro assump_26 assump_27 =>
                apply False.elim assump_26
  let assump_4 := assump_1 assump_33
  apply False.elim assump_4


variable (p6 p4 p0 p3 p5 p2 p7 : Prop)
theorem file92_37903 : ((((((p0 ∨ p2) ∧ (False → p2)) ∧ ((True ∧ False) ∧ (p0 → p3))) ∧ (((True → False) ∨ (p5 ∨ p0)) ∨ ((p0 ∧ p4) ∨ (p6 → False)))) ∧ ((((p7 ∧ p7) → False) ∨ ((p2 ∧ p3) ∧ (p2 → False))) ∨ (((True ∧ False) ∨ (p4 → p3)) → ((p6 ∧ True) → (False → False))))) → False) := by
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
                apply False.elim assump_19
          case inr assump_11 =>
            cases assump_7
            case intro assump_28 assump_29 =>
              cases assump_28
              case intro assump_30 assump_31 =>
                apply False.elim assump_31


variable (p6 p3 p0 : Prop)
theorem file92_38940 : (((((p6 ∧ False) → (False ∧ False)) → ((p0 → True) ∨ (p3 ∨ p6))) → False) → False) := by
  intro assump_1
  have assump_12 : (((p6 ∧ False) → (False ∧ False)) → ((p0 → True) ∨ (p3 ∨ p6))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    apply True.intro
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p7 p1 p0 p4 p3 : Prop)
theorem file92_39332 : (((((p1 → p3) → (True → True)) ∨ ((p7 ∨ p4) ∨ (False ∧ p0))) → False) → False) := by
  intro assump_1
  have assump_10 : (((p1 → p3) → (True → True)) ∨ ((p7 ∨ p4) ∨ (False ∧ p0))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    apply True.intro
  let assump_4 := assump_1 assump_10
  apply False.elim assump_4


variable (p1 p4 p2 p5 p7 : Prop)
theorem file92_39716 : ((((((True → False) ∨ (p4 ∨ p2)) → ((p1 → False) ∧ (p1 → p7))) → False) ∧ ((((p5 ∨ p1) → False) → ((True → False) → False)) → False)) → False) := by
  intro assump_68
  cases assump_68
  case intro assump_69 assump_70 =>
    have assump_90 : (((p5 ∨ p1) → False) → ((True → False) → False)) := by
      intro assump_76
      intro assump_77
      have assump_91 : True := by
        apply True.intro
      let assump_83 := assump_77 assump_91
      apply False.elim assump_83
    let assump_75 := assump_70 assump_90
    apply False.elim assump_75


variable (p3 p0 : Prop)
theorem file92_40312 : ((((((False → p3) → False) ∨ ((True ∨ p0) → False)) → False) → False) → False) := by
  intro assump_5
  have assump_30 : ((((False → p3) → False) ∨ ((True ∨ p0) → False)) → False) := by
    intro assump_9
    cases assump_9
    case inl assump_10 =>
      have assump_31 : (False → p3) := by
        intro assump_15
        apply False.elim assump_15
      let assump_14 := assump_10 assump_31
      apply False.elim assump_14
    case inr assump_11 =>
      have assump_32 : (True ∨ p0) := by
        apply Or.inl
        apply True.intro
      let assump_23 := assump_11 assump_32
      apply False.elim assump_23
  let assump_8 := assump_5 assump_30
  apply False.elim assump_8


variable (p4 p1 p6 p0 p5 p2 p3 : Prop)
theorem file92_41056 : (((((False ∧ p2) → False) ∨ ((p6 → p3) ∨ (p4 ∨ p3))) → (((True ∧ False) → False) ∨ ((True ∧ p3) → (False ∧ p6)))) ∨ ((((False → False) ∧ (p0 → p2)) ∧ ((p0 → p0) → (False ∨ p5))) ∨ (((p2 ∨ p1) → (False ∧ False)) ∧ ((p2 ∨ p2) ∨ (p4 → p0))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_8
  case inr assump_3 =>
    cases assump_3
    case inl assump_13 =>
      apply Or.inl
      intro assump_17
      cases assump_17
      case intro assump_18 assump_19 =>
        apply False.elim assump_19
    case inr assump_14 =>
      cases assump_14
      case inl assump_24 =>
        apply Or.inl
        intro assump_28
        cases assump_28
        case intro assump_29 assump_30 =>
          apply False.elim assump_30
      case inr assump_25 =>
        apply Or.inl
        intro assump_37
        cases assump_37
        case intro assump_38 assump_39 =>
          apply False.elim assump_39


variable (p4 p0 p1 p7 p2 p3 p6 : Prop)
theorem file92_42166 : (((((p7 ∧ p4) → (p4 ∨ p1)) → False) → (((p6 ∨ True) → False) ∧ ((p4 ∨ p2) → False))) ∨ ((((False ∧ p3) ∨ (p4 → True)) → False) → (((False ∧ p4) ∧ (p0 ∧ p6)) → False))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    have assump_68 : ((p7 ∧ p4) → (p4 ∨ p1)) := by
      intro assump_10
      cases assump_10
      case intro assump_11 assump_12 =>
        apply Or.inl
        exact assump_12
    let assump_9 := assump_1 assump_68
    apply False.elim assump_9
  case inr assump_4 =>
    have assump_69 : ((p7 ∧ p4) → (p4 ∨ p1)) := by
      intro assump_25
      cases assump_25
      case intro assump_26 assump_27 =>
        apply Or.inl
        exact assump_27
    let assump_24 := assump_1 assump_69
    apply False.elim assump_24
  intro assump_35
  cases assump_35
  case inl assump_36 =>
    have assump_70 : ((p7 ∧ p4) → (p4 ∨ p1)) := by
      intro assump_43
      cases assump_43
      case intro assump_44 assump_45 =>
        apply Or.inl
        exact assump_45
    let assump_42 := assump_1 assump_70
    apply False.elim assump_42
  case inr assump_37 =>
    have assump_71 : ((p7 ∧ p4) → (p4 ∨ p1)) := by
      intro assump_58
      cases assump_58
      case intro assump_59 assump_60 =>
        apply Or.inl
        exact assump_60
    let assump_57 := assump_1 assump_71
    apply False.elim assump_57


variable (p5 p4 p2 p7 p6 p1 p0 p3 : Prop)
theorem file92_43622 : ((((((p7 ∨ p7) ∧ (True → p6)) ∧ ((p1 → p0) ∧ (p1 → False))) ∧ (((p3 ∨ p4) ∧ (p1 ∧ False)) ∧ ((False → False) → False))) ∧ ((((p1 ∧ p2) → (p7 → p6)) → ((p3 → False) → False)) ∧ (((p0 → p4) ∧ (False → p5)) ∧ ((p4 → False) ∨ (p5 ∨ p1))))) → False) := by
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
              cases assump_5
              case intro assump_22 assump_23 =>
                cases assump_22
                case intro assump_24 assump_25 =>
                  cases assump_24
                  case inl assump_26 =>
                    cases assump_25
                    case intro assump_30 assump_31 =>
                      apply False.elim assump_31
                  case inr assump_27 =>
                    cases assump_25
                    case intro assump_38 assump_39 =>
                      apply False.elim assump_39
          case inr assump_11 =>
            cases assump_7
            case intro assump_48 assump_49 =>
              cases assump_5
              case intro assump_54 assump_55 =>
                cases assump_54
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


variable (p5 p6 : Prop)
theorem file92_45503 : (((((p6 ∨ p5) → False) → ((p5 ∧ False) → False)) → False) → False) := by
  intro assump_5
  have assump_20 : (((p6 ∨ p5) → False) → ((p5 ∧ False) → False)) := by
    intro assump_9
    intro assump_10
    cases assump_10
    case intro assump_11 assump_12 =>
      apply False.elim assump_12
  let assump_8 := assump_5 assump_20
  apply False.elim assump_8


variable (p0 p1 p4 p6 p5 : Prop)
theorem file92_45917 : (((((True → False) ∨ (True → False)) ∧ ((False ∨ p5) → (p5 ∨ p0))) → False) ∨ ((((p4 ∧ True) → (p6 → False)) → False) → (((p4 → True) → False) ∨ ((p6 ∧ p1) → False)))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_24 : True := by
        apply True.intro
      let assump_11 := assump_4 assump_24
      apply False.elim assump_11
    case inr assump_5 =>
      have assump_25 : True := by
        apply True.intro
      let assump_20 := assump_5 assump_25
      apply False.elim assump_20


variable (p4 p7 p2 p0 p6 p5 : Prop)
theorem file92_46571 : (((((True ∨ p5) → (False ∨ p6)) → ((p0 ∨ p4) ∧ (p7 ∧ p6))) → (((p7 ∨ p0) → False) ∧ ((False → p0) → (p5 → False)))) → ((((True → False) ∧ (p7 → False)) → ((p2 ∧ True) ∨ (p2 ∨ p2))) ∨ (((p7 ∨ p4) → False) → False))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    have assump_16 : True := by
      apply True.intro
    let assump_12 := assump_5 assump_16
    apply False.elim assump_12


variable (p2 p3 p4 p1 p5 p0 p7 p6 : Prop)
theorem file92_47084 : ((((((p0 ∨ p6) ∧ (p0 ∧ p7)) → ((False → False) ∧ (p7 → True))) → False) ∧ ((((p1 ∨ False) ∧ (p4 → p3)) ∨ ((p2 ∧ p6) → (p6 ∧ p0))) ∨ (((p5 ∧ p5) ∧ (False → p6)) → ((False ∧ p5) ∨ (p1 ∧ p4))))) → False) := by
  intro assump_19
  cases assump_19
  case intro assump_20 assump_21 =>
    cases assump_21
    case inl assump_24 =>
      cases assump_24
      case inl assump_26 =>
        cases assump_26
        case intro assump_28 assump_29 =>
          cases assump_28
          case inl assump_30 =>
            have assump_73 : (((p0 ∨ p6) ∧ (p0 ∧ p7)) → ((False → False) ∧ (p7 → True))) := by
              intro assump_39
              apply And.intro
              intro assump_40
              apply False.elim assump_40
              intro assump_43
              apply True.intro
            let assump_38 := assump_20 assump_73
            apply False.elim assump_38
          case inr assump_31 =>
            apply False.elim assump_31
      case inr assump_27 =>
        have assump_74 : (((p0 ∨ p6) ∧ (p0 ∧ p7)) → ((False → False) ∧ (p7 → True))) := by
          intro assump_53
          apply And.intro
          intro assump_54
          apply False.elim assump_54
          intro assump_57
          apply True.intro
        let assump_52 := assump_20 assump_74
        apply False.elim assump_52
    case inr assump_25 =>
      have assump_75 : (((p0 ∨ p6) ∧ (p0 ∧ p7)) → ((False → False) ∧ (p7 → True))) := by
        intro assump_65
        apply And.intro
        intro assump_66
        apply False.elim assump_66
        intro assump_69
        apply True.intro
      let assump_64 := assump_20 assump_75
      apply False.elim assump_64


variable (p1 p6 p0 p7 p3 : Prop)
theorem file92_48800 : (((((False ∧ p7) → (p0 ∧ p6)) → False) → False) ∨ ((((p3 → False) → False) ∨ ((p1 → False) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  have assump_17 : ((False ∧ p7) → (p0 ∧ p6)) := by
    intro assump_5
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
    cases assump_5
    case intro assump_10 assump_11 =>
      apply False.elim assump_10
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p1 p4 p7 p0 p6 p3 p5 p2 : Prop)
theorem file92_49348 : (((((p0 ∧ p6) ∧ (True → False)) → ((p1 → p2) ∧ (p4 → False))) ∨ (((True → False) ∧ (p0 → False)) ∨ ((p3 → False) ∧ (p3 ∧ p4)))) ∨ ((((p4 → p7) → False) ∨ ((p1 → p7) → False)) → (((False ∧ p5) → (p6 ∨ p5)) → ((p7 → False) ∨ (True → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      have assump_36 : True := by
        apply True.intro
      let assump_15 := assump_6 assump_36
      apply False.elim assump_15
  intro assump_19
  cases assump_1
  case intro assump_22 assump_23 =>
    cases assump_22
    case intro assump_24 assump_25 =>
      have assump_37 : True := by
        apply True.intro
      let assump_32 := assump_23 assump_37
      apply False.elim assump_32


variable (p6 p2 p7 p0 p1 p4 : Prop)
theorem file92_50242 : (((((p4 ∧ True) ∨ (p7 ∨ True)) → False) → False) ∨ ((((p4 → p1) ∨ (True → p0)) → ((False → False) → (p0 → p0))) → (((p6 → False) ∨ (p6 → True)) → ((p6 ∧ p4) ∨ (p2 → p6))))) := by
  apply Or.inl
  intro assump_1
  have assump_8 : ((p4 ∧ True) ∨ (p7 ∨ True)) := by
    apply Or.inr
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p0 p1 p5 p4 p6 p7 : Prop)
theorem file92_50684 : (((((p5 ∧ True) → (p4 → p0)) ∧ ((p1 ∧ p7) ∧ (p4 → False))) ∧ (((p7 → p6) → (True ∨ p1)) ∧ ((True ∧ True) → False))) → False) := by
  intro assump_20
  cases assump_20
  case intro assump_21 assump_22 =>
    cases assump_21
    case intro assump_23 assump_24 =>
      cases assump_24
      case intro assump_27 assump_28 =>
        cases assump_27
        case intro assump_29 assump_30 =>
          cases assump_22
          case intro assump_37 assump_38 =>
            have assump_47 : (True ∧ True) := by
              apply And.intro
              apply True.intro
              apply True.intro
            let assump_43 := assump_38 assump_47
            apply False.elim assump_43


variable (p5 p2 p4 p3 : Prop)
theorem file92_51426 : (((((p5 ∧ False) → False) ∧ ((p2 ∧ p4) → (p4 ∨ p3))) → False) → False) := by
  intro assump_7
  have assump_28 : (((p5 ∧ False) → False) ∧ ((p2 ∧ p4) → (p4 ∨ p3))) := by
    apply And.intro
    intro assump_11
    cases assump_11
    case intro assump_12 assump_13 =>
      apply False.elim assump_13
    intro assump_18
    cases assump_18
    case intro assump_19 assump_20 =>
      apply Or.inl
      exact assump_20
  let assump_10 := assump_7 assump_28
  apply False.elim assump_10


variable (p3 p5 p7 p1 : Prop)
theorem file92_51967 : (((((p5 → p1) → (p3 ∧ True)) → ((p7 ∧ False) → False)) → False) → False) := by
  intro assump_1
  have assump_16 : (((p5 → p1) → (p3 ∧ True)) → ((p7 ∧ False) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_8
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p1 p3 p0 p7 p6 p5 p2 : Prop)
theorem file92_52394 : ((((((p5 ∨ p2) → False) ∨ ((p1 ∧ p7) → (False → False))) → False) ∧ ((((True → False) → False) → ((False ∨ False) ∧ (False → p0))) ∧ (((p7 ∨ p1) → False) ∨ ((p6 → False) ∧ (p2 ∨ p3))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        have assump_77 : ((True → False) → False) := by
          intro assump_16
          have assump_78 : True := by
            apply True.intro
          let assump_19 := assump_16 assump_78
          apply False.elim assump_19
        let assump_15 := assump_6 assump_77
        let assump_23 := And.left assump_15
        cases assump_23
        case inl assump_25 =>
          apply False.elim assump_25
        case inr assump_26 =>
          apply False.elim assump_26
      case inr assump_11 =>
        cases assump_11
        case intro assump_31 assump_32 =>
          cases assump_32
          case inl assump_35 =>
            have assump_79 : ((True → False) → False) := by
              intro assump_42
              have assump_80 : True := by
                apply True.intro
              let assump_45 := assump_42 assump_80
              apply False.elim assump_45
            let assump_41 := assump_6 assump_79
            let assump_49 := And.left assump_41
            cases assump_49
            case inl assump_51 =>
              apply False.elim assump_51
            case inr assump_52 =>
              apply False.elim assump_52
          case inr assump_36 =>
            have assump_81 : ((True → False) → False) := by
              intro assump_62
              have assump_82 : True := by
                apply True.intro
              let assump_65 := assump_62 assump_82
              apply False.elim assump_65
            let assump_61 := assump_6 assump_81
            let assump_69 := And.left assump_61
            cases assump_69
            case inl assump_71 =>
              apply False.elim assump_71
            case inr assump_72 =>
              apply False.elim assump_72


variable (p4 p5 p2 p0 p7 p6 : Prop)
theorem file92_54552 : ((((((p2 ∨ True) → (True ∨ True)) → False) ∧ (((p2 → p7) ∧ (p2 → p7)) ∧ ((p7 → p0) ∨ (p4 → p7)))) ∨ ((((p6 → False) → (p6 → p5)) → False) ∧ (((True → False) → (p0 ∧ p6)) ∧ ((p0 → p0) → (True → False))))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_9
          case inl assump_16 =>
            have assump_68 : ((p2 ∨ True) → (True ∨ True)) := by
              intro assump_24
              cases assump_24
              case inl assump_25 =>
                apply Or.inl
                apply True.intro
              case inr assump_26 =>
                apply Or.inl
                apply True.intro
            let assump_23 := assump_4 assump_68
            apply False.elim assump_23
          case inr assump_17 =>
            have assump_69 : ((p2 ∨ True) → (True ∨ True)) := by
              intro assump_40
              cases assump_40
              case inl assump_41 =>
                apply Or.inl
                apply True.intro
              case inr assump_42 =>
                apply Or.inl
                apply True.intro
            let assump_39 := assump_4 assump_69
            apply False.elim assump_39
  case inr assump_3 =>
    cases assump_3
    case intro assump_50 assump_51 =>
      cases assump_51
      case intro assump_54 assump_55 =>
        have assump_70 : (p0 → p0) := by
          intro assump_61
          exact assump_61
        let assump_60 := assump_55 assump_70
        have assump_71 : True := by
          apply True.intro
        let assump_64 := assump_60 assump_71
        apply False.elim assump_64


variable (p4 p0 p7 p6 p3 p5 : Prop)
theorem file92_56395 : (((((p3 → False) ∨ (p7 → False)) ∨ ((p3 ∨ p7) → (p4 → p3))) ∧ (((False → False) → (False ∧ p4)) ∧ ((p5 → p6) ∨ (p3 → p0)))) → False) := by
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
          case inl assump_18 =>
            have assump_102 : (False → False) := by
              intro assump_24
              apply False.elim assump_24
            let assump_23 := assump_14 assump_102
            let assump_27 := And.left assump_23
            apply False.elim assump_27
          case inr assump_19 =>
            have assump_103 : (False → False) := by
              intro assump_35
              apply False.elim assump_35
            let assump_34 := assump_14 assump_103
            let assump_38 := And.left assump_34
            apply False.elim assump_38
      case inr assump_11 =>
        cases assump_7
        case intro assump_44 assump_45 =>
          cases assump_45
          case inl assump_48 =>
            have assump_104 : (False → False) := by
              intro assump_54
              apply False.elim assump_54
            let assump_53 := assump_44 assump_104
            let assump_57 := And.left assump_53
            apply False.elim assump_57
          case inr assump_49 =>
            have assump_105 : (False → False) := by
              intro assump_65
              apply False.elim assump_65
            let assump_64 := assump_44 assump_105
            let assump_68 := And.left assump_64
            apply False.elim assump_68
    case inr assump_9 =>
      cases assump_7
      case intro assump_74 assump_75 =>
        cases assump_75
        case inl assump_78 =>
          have assump_106 : (False → False) := by
            intro assump_84
            apply False.elim assump_84
          let assump_83 := assump_74 assump_106
          let assump_87 := And.left assump_83
          apply False.elim assump_87
        case inr assump_79 =>
          have assump_107 : (False → False) := by
            intro assump_95
            apply False.elim assump_95
          let assump_94 := assump_74 assump_107
          let assump_98 := And.left assump_94
          apply False.elim assump_98


variable (p3 p6 p5 p2 : Prop)
theorem file92_58793 : ((((((False ∧ p3) → False) ∨ ((p6 → True) → (p5 → False))) ∨ (((p5 → False) → False) ∧ ((p3 ∧ p2) ∧ (False ∨ p3)))) → False) → False) := by
  intro assump_1
  have assump_13 : ((((False ∧ p3) → False) ∨ ((p6 → True) → (p5 → False))) ∨ (((p5 → False) → False) ∧ ((p3 ∧ p2) ∧ (False ∨ p3)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p4 p7 p5 p3 p6 p1 p2 : Prop)
theorem file92_59357 : ((((((p4 ∨ p5) → (p7 ∧ True)) → ((p6 ∨ p6) → False)) → (((p3 → True) ∨ (p4 → p1)) ∨ ((p4 ∨ p2) → False))) → False) → False) := by
  intro assump_1
  have assump_12 : ((((p4 ∨ p5) → (p7 ∧ True)) → ((p6 ∨ p6) → False)) → (((p3 → True) ∨ (p4 → p1)) ∨ ((p4 ∨ p2) → False))) := by
    intro assump_5
    apply Or.inl
    apply Or.inl
    intro assump_8
    apply True.intro
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p2 p6 p3 p1 p5 p0 : Prop)
theorem file92_59851 : ((((((p1 → False) → False) ∧ ((p2 ∧ p0) ∨ (p5 → p6))) ∨ (((p1 → p0) ∧ (False ∨ p3)) → False)) ∧ ((((False ∧ p5) → False) → False) ∧ (((False → p1) → False) ∧ ((p1 ∧ p5) → (False ∨ p0))))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case inl assump_8 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        cases assump_11
        case inl assump_14 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            cases assump_7
            case intro assump_22 assump_23 =>
              cases assump_23
              case intro assump_26 assump_27 =>
                have assump_80 : (False → p1) := by
                  intro assump_34
                  apply False.elim assump_34
                let assump_33 := assump_26 assump_80
                apply False.elim assump_33
        case inr assump_15 =>
          cases assump_7
          case intro assump_42 assump_43 =>
            cases assump_43
            case intro assump_46 assump_47 =>
              have assump_81 : (False → p1) := by
                intro assump_54
                apply False.elim assump_54
              let assump_53 := assump_46 assump_81
              apply False.elim assump_53
    case inr assump_9 =>
      cases assump_7
      case intro assump_62 assump_63 =>
        cases assump_63
        case intro assump_66 assump_67 =>
          have assump_82 : (False → p1) := by
            intro assump_74
            apply False.elim assump_74
          let assump_73 := assump_66 assump_82
          apply False.elim assump_73


variable (p1 p5 p0 p2 p6 p7 : Prop)
theorem file92_61528 : (((((p7 ∨ p5) → False) ∧ ((p0 ∧ p7) ∧ (p1 ∨ p7))) → False) ∨ ((((p6 → p5) ∨ (p2 → p1)) → False) → (((p5 ∨ p0) ∨ (p2 ∨ p6)) → ((True → p0) → (p2 → p2))))) := by
  apply Or.inl
  intro assump_32
  cases assump_32
  case intro assump_33 assump_34 =>
    cases assump_34
    case intro assump_37 assump_38 =>
      cases assump_37
      case intro assump_39 assump_40 =>
        cases assump_38
        case inl assump_45 =>
          have assump_65 : (p7 ∨ p5) := by
            apply Or.inl
            exact assump_40
          let assump_52 := assump_33 assump_65
          apply False.elim assump_52
        case inr assump_46 =>
          have assump_66 : (p7 ∨ p5) := by
            apply Or.inl
            exact assump_46
          let assump_61 := assump_33 assump_66
          apply False.elim assump_61


variable (p6 p3 p2 p0 p1 p4 p7 p5 : Prop)
theorem file92_62405 : (((((p7 → p7) ∨ (p1 → p3)) → ((p5 → p7) → (False ∧ p6))) ∧ (((p7 ∨ True) → False) ∧ ((p2 → p2) → (p1 → False)))) → ((((p0 ∨ p2) → False) ∨ ((p4 → False) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        have assump_47 : (p7 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_22 := assump_11 assump_47
        apply False.elim assump_22
  case inr assump_4 =>
    cases assump_1
    case intro assump_28 assump_29 =>
      cases assump_29
      case intro assump_32 assump_33 =>
        have assump_48 : (p7 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_43 := assump_32 assump_48
        apply False.elim assump_43


variable (p1 p3 p6 p0 : Prop)
theorem file92_63316 : (((((False ∧ p0) → (p6 ∧ p3)) ∨ ((True ∧ p6) → False)) → False) → ((((p6 ∧ p1) ∧ (p3 → False)) → False) → False)) := by
  intro assump_1
  intro assump_2
  have assump_20 : (((False ∧ p0) → (p6 ∧ p3)) ∨ ((True ∧ p6) → False)) := by
    apply Or.inl
    intro assump_8
    apply And.intro
    cases assump_8
    case intro assump_9 assump_10 =>
      apply False.elim assump_9
    cases assump_8
    case intro assump_13 assump_14 =>
      apply False.elim assump_13
  let assump_7 := assump_1 assump_20
  apply False.elim assump_7


variable (p4 p2 p0 : Prop)
theorem file92_63898 : ((((((p2 → p2) ∨ (p2 ∧ True)) ∨ ((p4 → False) → False)) ∨ (((p4 ∧ p0) → (False ∨ False)) → False)) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p2 → p2) ∨ (p2 ∧ True)) ∨ ((p4 → False) → False)) ∨ (((p4 ∧ p0) → (False ∨ False)) → False)) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    intro assump_5
    exact assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p5 p3 p0 p6 p4 p2 : Prop)
theorem file92_64374 : (((((p4 → False) → (p4 ∧ p3)) → False) → (((True ∧ p5) ∧ (False → False)) ∨ ((p4 ∧ True) → (p5 → False)))) ∨ ((((p4 → p0) → False) ∧ ((True ∧ p4) ∧ (p6 ∨ False))) ∧ (((p3 ∨ p2) ∨ (p3 → p5)) → False))) := by
  apply Or.inl
  intro assump_13
  apply Or.inr
  intro assump_16
  intro assump_17
  cases assump_16
  case intro assump_20 assump_21 =>
    have assump_41 : ((p4 → False) → (p4 ∧ p3)) := by
      intro assump_29
      apply And.intro
      exact assump_20
      have assump_42 : p4 := by
        exact assump_20
      let assump_34 := assump_29 assump_42
      apply False.elim assump_34
    let assump_28 := assump_13 assump_41
    apply False.elim assump_28


variable (p4 p2 p3 p5 p6 p0 p7 : Prop)
theorem file92_65106 : ((((((p5 → False) → False) ∧ ((p6 ∨ p4) → (p7 ∧ p7))) ∨ (((p7 ∧ p4) ∧ (p2 ∨ p3)) → ((p2 → False) ∨ (p6 → False)))) ∧ ((((True ∧ p5) ∨ (True ∧ p7)) ∨ ((False → p0) → (p5 → p5))) → False)) → False) := by
  intro assump_8
  cases assump_8
  case intro assump_9 assump_10 =>
    cases assump_9
    case inl assump_11 =>
      cases assump_11
      case intro assump_13 assump_14 =>
        have assump_45 : (((True ∧ p5) ∨ (True ∧ p7)) ∨ ((False → p0) → (p5 → p5))) := by
          apply Or.inr
          intro assump_22
          intro assump_23
          exact assump_23
        let assump_21 := assump_10 assump_45
        apply False.elim assump_21
    case inr assump_12 =>
      have assump_46 : (((True ∧ p5) ∨ (True ∧ p7)) ∨ ((False → p0) → (p5 → p5))) := by
        apply Or.inr
        intro assump_36
        intro assump_37
        exact assump_37
      let assump_35 := assump_10 assump_46
      apply False.elim assump_35


variable (p4 p3 p6 p0 p5 p7 p2 : Prop)
theorem file92_66101 : (((((p7 → p4) ∨ (p5 ∧ p0)) → False) → False) → ((((p3 → False) → (p4 → False)) → ((True → False) → (False → False))) ∨ (((p3 ∧ p6) → False) ∨ ((False → p2) ∨ (p4 ∨ p4))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  intro assump_6
  apply False.elim assump_6


variable (p0 p4 p1 p6 p2 : Prop)
theorem file92_66447 : (((((False → True) → (True ∧ True)) ∨ ((p2 ∨ p4) → False)) ∨ (((p1 ∨ p2) ∨ (False ∧ p0)) → False)) ∨ ((((p4 ∨ p1) → False) ∨ ((p4 ∧ p1) ∨ (p6 ∧ p0))) → (((p4 → p4) → False) → False))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply And.intro
  apply True.intro
  apply True.intro


variable (p5 p1 p7 p3 p2 p0 : Prop)
theorem file92_66815 : (((((p1 → False) ∨ (p0 ∧ False)) ∨ ((p3 → p5) → (p1 → p5))) → (((True ∨ True) ∧ (p3 → False)) → ((p7 → False) → (p2 ∨ True)))) ∧ ((((True → False) → False) → False) → False)) := by
  apply And.intro
  intro assump_22
  intro assump_23
  intro assump_24
  cases assump_23
  case intro assump_27 assump_28 =>
    cases assump_27
    case inl assump_29 =>
      cases assump_22
      case inl assump_35 =>
        cases assump_35
        case inl assump_37 =>
          apply Or.inr
          apply True.intro
        case inr assump_38 =>
          cases assump_38
          case intro assump_41 assump_42 =>
            apply False.elim assump_42
      case inr assump_36 =>
        apply Or.inr
        apply True.intro
    case inr assump_30 =>
      cases assump_22
      case inl assump_53 =>
        cases assump_53
        case inl assump_55 =>
          apply Or.inr
          apply True.intro
        case inr assump_56 =>
          cases assump_56
          case intro assump_59 assump_60 =>
            apply False.elim assump_60
      case inr assump_54 =>
        apply Or.inr
        apply True.intro
  intro assump_67
  have assump_81 : ((True → False) → False) := by
    intro assump_71
    have assump_82 : True := by
      apply True.intro
    let assump_74 := assump_71 assump_82
    apply False.elim assump_74
  let assump_70 := assump_67 assump_81
  apply False.elim assump_70


variable (p3 p4 p0 p7 p5 : Prop)
theorem file92_68268 : ((((((p5 → False) → (p0 → False)) → ((False → False) ∧ (p5 → p5))) ∨ (((p5 ∧ p4) ∧ (True ∨ p7)) ∨ ((True → p5) ∨ (p3 ∧ True)))) → False) → False) := by
  intro assump_1
  have assump_17 : ((((p5 → False) → (p0 → False)) → ((False → False) ∧ (p5 → p5))) ∨ (((p5 ∧ p4) ∧ (True ∨ p7)) ∨ ((True → p5) ∨ (p3 ∧ True)))) := by
    apply Or.inl
    intro assump_5
    apply And.intro
    intro assump_6
    apply False.elim assump_6
    intro assump_9
    exact assump_9
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p3 p1 p7 p6 p4 p0 p2 : Prop)
theorem file92_68859 : (((((True ∧ p0) ∨ (p3 ∨ p7)) ∨ ((p7 → p7) ∧ (p1 ∨ True))) → False) → ((((p2 → p1) → (p4 ∧ False)) ∧ ((p2 ∧ p0) → False)) ∧ (((p3 ∧ p2) → False) ∨ ((p6 → p7) ∨ (True → False))))) := by
  intro assump_7
  apply And.intro
  apply And.intro
  intro assump_8
  apply And.intro
  have assump_59 : (((True ∧ p0) ∨ (p3 ∨ p7)) ∨ ((p7 → p7) ∧ (p1 ∨ True))) := by
    apply Or.inr
    apply And.intro
    intro assump_14
    exact assump_14
    apply Or.inr
    apply True.intro
  let assump_13 := assump_7 assump_59
  apply False.elim assump_13
  have assump_60 : (((True ∧ p0) ∨ (p3 ∨ p7)) ∨ ((p7 → p7) ∧ (p1 ∨ True))) := by
    apply Or.inr
    apply And.intro
    intro assump_25
    exact assump_25
    apply Or.inr
    apply True.intro
  let assump_24 := assump_7 assump_60
  apply False.elim assump_24
  intro assump_31
  cases assump_31
  case intro assump_32 assump_33 =>
    have assump_61 : (((True ∧ p0) ∨ (p3 ∨ p7)) ∨ ((p7 → p7) ∧ (p1 ∨ True))) := by
      apply Or.inl
      apply Or.inl
      apply And.intro
      apply True.intro
      exact assump_33
    let assump_40 := assump_7 assump_61
    apply False.elim assump_40
  apply Or.inl
  intro assump_46
  cases assump_46
  case intro assump_47 assump_48 =>
    have assump_62 : (((True ∧ p0) ∨ (p3 ∨ p7)) ∨ ((p7 → p7) ∧ (p1 ∨ True))) := by
      apply Or.inl
      apply Or.inr
      apply Or.inl
      exact assump_47
    let assump_55 := assump_7 assump_62
    apply False.elim assump_55


variable (p4 p3 p6 p7 p0 p1 p2 : Prop)
theorem file92_70371 : ((((((p0 → False) → (p6 → True)) → ((False → p4) ∨ (p7 ∧ p3))) ∨ (((p1 → p4) → (p7 → p2)) → ((p0 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p0 → False) → (p6 → True)) → ((False → p4) ∨ (p7 ∧ p3))) ∨ (((p1 → p4) → (p7 → p2)) → ((p0 → False) → False))) := by
    apply Or.inl
    intro assump_5
    apply Or.inl
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p7 p3 p2 p4 p1 p0 p5 : Prop)
theorem file92_70899 : (((((p7 ∧ p4) → False) → ((p0 ∨ p2) ∨ (p1 → p5))) ∧ (((True ∨ p4) ∧ (False → False)) → False)) → ((((True ∧ p1) → (p5 ∧ p2)) → ((p0 → p1) ∧ (p2 ∧ True))) ∨ (((p0 → False) ∨ (p3 → False)) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    intro assump_8
    apply And.intro
    intro assump_9
    have assump_33 : ((True ∨ p4) ∧ (False → False)) := by
      apply And.intro
      apply Or.inl
      apply True.intro
      intro assump_17
      apply False.elim assump_17
    let assump_16 := assump_3 assump_33
    apply False.elim assump_16
    apply And.intro
    have assump_34 : ((True ∨ p4) ∧ (False → False)) := by
      apply And.intro
      apply Or.inl
      apply True.intro
      intro assump_27
      apply False.elim assump_27
    let assump_26 := assump_3 assump_34
    apply False.elim assump_26
    apply True.intro


variable (p4 p2 p7 p0 p6 p3 p1 : Prop)
theorem file92_71848 : (((((p1 → False) ∧ (p2 ∧ p0)) → ((p2 → False) → (p4 → p6))) ∨ (((p4 → p2) → (p7 → p3)) ∧ ((p1 ∧ p1) → (p6 → False)))) ∨ ((((p3 ∧ False) ∨ (p2 → p0)) → ((p7 ∧ False) → False)) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_1
  case intro assump_8 assump_9 =>
    cases assump_9
    case intro assump_12 assump_13 =>
      have assump_25 : p2 := by
        exact assump_12
      let assump_21 := assump_2 assump_25
      apply False.elim assump_21


variable (p3 p7 p1 p0 p5 p2 p4 : Prop)
theorem file92_72422 : (((((p0 → p0) ∨ (p4 ∧ p7)) → ((p4 → False) → False)) → (((p5 ∨ p2) → False) ∨ ((True ∧ p3) → False))) → ((((p1 ∧ False) ∧ (True ∧ p5)) ∧ ((p2 ∧ p7) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        apply False.elim assump_8


variable (p7 p2 p6 p1 p4 p5 : Prop)
theorem file92_72889 : (((((True ∨ p7) ∨ (p4 ∧ p7)) ∨ ((p2 → False) → False)) ∧ (((p5 ∧ p6) ∨ (p4 → p4)) ∨ ((p4 ∧ p2) → False))) ∨ ((((False → False) → (p6 ∧ p6)) ∧ ((p6 ∨ p6) → (p1 ∧ True))) ∧ (((p1 ∨ p5) → False) → False))) := by
  apply Or.inl
  apply And.intro
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply True.intro
  apply Or.inl
  apply Or.inr
  intro assump_1
  exact assump_1


variable (p6 p1 p4 p5 p2 : Prop)
theorem file92_73316 : (((((p1 ∨ True) ∧ (True → False)) ∧ ((p5 ∧ False) ∧ (True → False))) → (((p6 ∧ p4) → False) → False)) ∨ ((((p2 ∧ p4) ∧ (p2 → p1)) → ((False → False) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_6
        case intro assump_15 assump_16 =>
          cases assump_15
          case intro assump_17 assump_18 =>
            apply False.elim assump_18
      case inr assump_10 =>
        cases assump_6
        case intro assump_27 assump_28 =>
          cases assump_27
          case intro assump_29 assump_30 =>
            apply False.elim assump_30


variable (p1 p5 p4 p6 p2 p3 p0 p7 : Prop)
theorem file92_74136 : (((((p5 ∨ p7) → (p7 → p7)) → False) → (((p1 ∨ p7) ∧ (p3 ∨ p5)) → False)) → ((((False ∨ False) ∧ (p7 ∧ p7)) ∧ ((True ∨ False) ∨ (p2 ∧ False))) → (((p5 → p2) ∧ (p6 ∧ p2)) ∨ ((p6 → p0) → (p4 → p0))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case inl assump_7 =>
        apply False.elim assump_7
      case inr assump_8 =>
        apply False.elim assump_8


variable (p0 p5 p3 p7 p2 : Prop)
theorem file92_74680 : ((((((p0 → False) → (p3 → p2)) → False) → (((False → p7) ∨ (False ∨ False)) ∧ ((p0 ∧ p5) → False))) → False) → False) := by
  intro assump_1
  have assump_37 : ((((p0 → False) → (p3 → p2)) → False) → (((False → p7) ∨ (False ∨ False)) ∧ ((p0 ∧ p5) → False))) := by
    intro assump_5
    apply And.intro
    apply Or.inl
    intro assump_8
    apply False.elim assump_8
    intro assump_11
    cases assump_11
    case intro assump_12 assump_13 =>
      have assump_38 : ((p0 → False) → (p3 → p2)) := by
        intro assump_21
        intro assump_22
        have assump_39 : p0 := by
          exact assump_12
        let assump_27 := assump_21 assump_39
        apply False.elim assump_27
      let assump_20 := assump_5 assump_38
      apply False.elim assump_20
  let assump_4 := assump_1 assump_37
  apply False.elim assump_4


variable (p7 p5 p0 p6 p1 p3 p2 p4 : Prop)
theorem file92_75577 : (((((p5 ∧ False) → False) ∨ ((True → False) → (True ∧ p7))) ∧ (((p1 → p3) → False) → ((p4 ∨ p0) → (p2 → True)))) ∨ ((((p7 → p5) → (p0 ∨ p4)) → False) → (((p7 ∨ p4) → (p6 ∧ p0)) ∨ ((False → p3) ∨ (p5 → p4))))) := by
  apply Or.inl
  apply And.intro
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply False.elim assump_3
  intro assump_8
  intro assump_9
  intro assump_10
  apply True.intro


variable (p4 p5 p7 p0 p3 p1 p6 : Prop)
theorem file92_76072 : (((((True ∧ p3) ∧ (p4 ∧ p6)) ∨ ((p4 ∨ p6) → (True → False))) ∧ (((p7 → True) ∨ (p4 ∨ p4)) ∨ ((p3 → False) → False))) → ((((p4 ∧ p6) ∧ (p0 ∧ p5)) → False) → (((p1 → p6) ∧ (p4 ∧ False)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_5
    case intro assump_8 assump_9 =>
      apply False.elim assump_9


variable (p4 p1 p5 p6 p0 p3 p7 : Prop)
theorem file92_76525 : ((((((p1 ∨ p1) ∧ (True → p1)) → ((False ∨ p4) ∨ (p4 → False))) → False) ∧ ((((p1 → p6) ∧ (p0 → False)) ∨ ((p3 ∧ p0) ∧ (p1 ∨ p7))) ∨ (((p1 ∧ p3) ∨ (p6 ∧ p5)) ∨ ((p5 → False) ∨ (p3 ∨ True))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          have assump_620 : (((p1 ∨ p1) ∧ (True → p1)) → ((False ∨ p4) ∨ (p4 → False))) := by
            intro assump_19
            cases assump_19
            case intro assump_20 assump_21 =>
              cases assump_20
              case inl assump_22 =>
                apply Or.inr
                intro assump_28
                have assump_621 : (((p1 ∨ p1) ∧ (True → p1)) → ((False ∨ p4) ∨ (p4 → False))) := by
                  intro assump_39
                  cases assump_39
                  case intro assump_40 assump_41 =>
                    cases assump_40
                    case inl assump_42 =>
                      apply Or.inl
                      apply Or.inr
                      exact assump_28
                    case inr assump_43 =>
                      apply Or.inl
                      apply Or.inr
                      exact assump_28
                let assump_38 := assump_2 assump_621
                apply False.elim assump_38
              case inr assump_23 =>
                apply Or.inr
                intro assump_59
                have assump_622 : (((p1 ∨ p1) ∧ (True → p1)) → ((False ∨ p4) ∨ (p4 → False))) := by
                  intro assump_70
                  cases assump_70
                  case intro assump_71 assump_72 =>
                    cases assump_71
                    case inl assump_73 =>
                      apply Or.inl
                      apply Or.inr
                      exact assump_59
                    case inr assump_74 =>
                      apply Or.inl
                      apply Or.inr
                      exact assump_59
                let assump_69 := assump_2 assump_622
                apply False.elim assump_69
          let assump_18 := assump_2 assump_620
          apply False.elim assump_18
      case inr assump_9 =>
        cases assump_9
        case intro assump_89 assump_90 =>
          cases assump_89
          case intro assump_91 assump_92 =>
            cases assump_90
            case inl assump_97 =>
              have assump_623 : (((p1 ∨ p1) ∧ (True → p1)) → ((False ∨ p4) ∨ (p4 → False))) := by
                intro assump_105
                cases assump_105
                case intro assump_106 assump_107 =>
                  cases assump_106
                  case inl assump_108 =>
                    apply Or.inr
                    intro assump_114
                    have assump_624 : (((p1 ∨ p1) ∧ (True → p1)) → ((False ∨ p4) ∨ (p4 → False))) := by
                      intro assump_125
                      cases assump_125
                      case intro assump_126 assump_127 =>
                        cases assump_126
                        case inl assump_128 =>
                          apply Or.inl
                          apply Or.inr
                          exact assump_114
                        case inr assump_129 =>
                          apply Or.inl
                          apply Or.inr
                          exact assump_114
                    let assump_124 := assump_2 assump_624
                    apply False.elim assump_124
                  case inr assump_109 =>
                    apply Or.inr
                    intro assump_145
                    have assump_625 : (((p1 ∨ p1) ∧ (True → p1)) → ((False ∨ p4) ∨ (p4 → False))) := by
                      intro assump_156
                      cases assump_156
                      case intro assump_157 assump_158 =>
                        cases assump_157
                        case inl assump_159 =>
                          apply Or.inl
                          apply Or.inr
                          exact assump_145
                        case inr assump_160 =>
                          apply Or.inl
                          apply Or.inr
                          exact assump_145
                    let assump_155 := assump_2 assump_625
                    apply False.elim assump_155
              let assump_104 := assump_2 assump_623
              apply False.elim assump_104
            case inr assump_98 =>
              have assump_626 : (((p1 ∨ p1) ∧ (True → p1)) → ((False ∨ p4) ∨ (p4 → False))) := by
                intro assump_181
                cases assump_181
                case intro assump_182 assump_183 =>
                  cases assump_182
                  case inl assump_184 =>
                    apply Or.inr
                    intro assump_190
                    have assump_627 : (((p1 ∨ p1) ∧ (True → p1)) → ((False ∨ p4) ∨ (p4 → False))) := by
                      intro assump_201
                      cases assump_201
                      case intro assump_202 assump_203 =>
                        cases assump_202
                        case inl assump_204 =>
                          apply Or.inl
                          apply Or.inr
                          exact assump_190
                        case inr assump_205 =>
                          apply Or.inl
                          apply Or.inr
                          exact assump_190
                    let assump_200 := assump_2 assump_627
                    apply False.elim assump_200
                  case inr assump_185 =>
                    apply Or.inr
                    intro assump_221
                    have assump_628 : (((p1 ∨ p1) ∧ (True → p1)) → ((False ∨ p4) ∨ (p4 → False))) := by
                      intro assump_232
                      cases assump_232
                      case intro assump_233 assump_234 =>
                        cases assump_233
                        case inl assump_235 =>
                          apply Or.inl
                          apply Or.inr
                          exact assump_221
                        case inr assump_236 =>
                          apply Or.inl
                          apply Or.inr
                          exact assump_221
                    let assump_231 := assump_2 assump_628
                    apply False.elim assump_231
              let assump_180 := assump_2 assump_626
              apply False.elim assump_180
    case inr assump_7 =>
      cases assump_7
      case inl assump_251 =>
        cases assump_251
        case inl assump_253 =>
          cases assump_253
          case intro assump_255 assump_256 =>
            have assump_629 : (((p1 ∨ p1) ∧ (True → p1)) → ((False ∨ p4) ∨ (p4 → False))) := by
              intro assump_264
              cases assump_264
              case intro assump_265 assump_266 =>
                cases assump_265
                case inl assump_267 =>
                  apply Or.inr
                  intro assump_273
                  have assump_630 : (((p1 ∨ p1) ∧ (True → p1)) → ((False ∨ p4) ∨ (p4 → False))) := by
                    intro assump_283
                    cases assump_283
                    case intro assump_284 assump_285 =>
                      cases assump_284
                      case inl assump_286 =>
                        apply Or.inl
                        apply Or.inr
                        exact assump_273
                      case inr assump_287 =>
                        apply Or.inl
                        apply Or.inr
                        exact assump_273
                  let assump_282 := assump_2 assump_630
                  apply False.elim assump_282
                case inr assump_268 =>
                  apply Or.inr
                  intro assump_303
                  have assump_631 : (((p1 ∨ p1) ∧ (True → p1)) → ((False ∨ p4) ∨ (p4 → False))) := by
                    intro assump_313
                    cases assump_313
                    case intro assump_314 assump_315 =>
                      cases assump_314
                      case inl assump_316 =>
                        apply Or.inl
                        apply Or.inr
                        exact assump_303
                      case inr assump_317 =>
                        apply Or.inl
                        apply Or.inr
                        exact assump_303
                  let assump_312 := assump_2 assump_631
                  apply False.elim assump_312
            let assump_263 := assump_2 assump_629
            apply False.elim assump_263
        case inr assump_254 =>
          cases assump_254
          case intro assump_332 assump_333 =>
            have assump_632 : (((p1 ∨ p1) ∧ (True → p1)) → ((False ∨ p4) ∨ (p4 → False))) := by
              intro assump_341
              cases assump_341
              case intro assump_342 assump_343 =>
                cases assump_342
                case inl assump_344 =>
                  apply Or.inr
                  intro assump_350
                  have assump_633 : (((p1 ∨ p1) ∧ (True → p1)) → ((False ∨ p4) ∨ (p4 → False))) := by
                    intro assump_360
                    cases assump_360
                    case intro assump_361 assump_362 =>
                      cases assump_361
                      case inl assump_363 =>
                        apply Or.inl
                        apply Or.inr
                        exact assump_350
                      case inr assump_364 =>
                        apply Or.inl
                        apply Or.inr
                        exact assump_350
                  let assump_359 := assump_2 assump_633
                  apply False.elim assump_359
                case inr assump_345 =>
                  apply Or.inr
                  intro assump_380
                  have assump_634 : (((p1 ∨ p1) ∧ (True → p1)) → ((False ∨ p4) ∨ (p4 → False))) := by
                    intro assump_390
                    cases assump_390
                    case intro assump_391 assump_392 =>
                      cases assump_391
                      case inl assump_393 =>
                        apply Or.inl
                        apply Or.inr
                        exact assump_380
                      case inr assump_394 =>
                        apply Or.inl
                        apply Or.inr
                        exact assump_380
                  let assump_389 := assump_2 assump_634
                  apply False.elim assump_389
            let assump_340 := assump_2 assump_632
            apply False.elim assump_340
      case inr assump_252 =>
        cases assump_252
        case inl assump_409 =>
          have assump_635 : (((p1 ∨ p1) ∧ (True → p1)) → ((False ∨ p4) ∨ (p4 → False))) := by
            intro assump_415
            cases assump_415
            case intro assump_416 assump_417 =>
              cases assump_416
              case inl assump_418 =>
                apply Or.inr
                intro assump_424
                have assump_636 : (((p1 ∨ p1) ∧ (True → p1)) → ((False ∨ p4) ∨ (p4 → False))) := by
                  intro assump_433
                  cases assump_433
                  case intro assump_434 assump_435 =>
                    cases assump_434
                    case inl assump_436 =>
                      apply Or.inl
                      apply Or.inr
                      exact assump_424
                    case inr assump_437 =>
                      apply Or.inl
                      apply Or.inr
                      exact assump_424
                let assump_432 := assump_2 assump_636
                apply False.elim assump_432
              case inr assump_419 =>
                apply Or.inr
                intro assump_453
                have assump_637 : (((p1 ∨ p1) ∧ (True → p1)) → ((False ∨ p4) ∨ (p4 → False))) := by
                  intro assump_462
                  cases assump_462
                  case intro assump_463 assump_464 =>
                    cases assump_463
                    case inl assump_465 =>
                      apply Or.inl
                      apply Or.inr
                      exact assump_453
                    case inr assump_466 =>
                      apply Or.inl
                      apply Or.inr
                      exact assump_453
                let assump_461 := assump_2 assump_637
                apply False.elim assump_461
          let assump_414 := assump_2 assump_635
          apply False.elim assump_414
        case inr assump_410 =>
          cases assump_410
          case inl assump_481 =>
            have assump_638 : (((p1 ∨ p1) ∧ (True → p1)) → ((False ∨ p4) ∨ (p4 → False))) := by
              intro assump_487
              cases assump_487
              case intro assump_488 assump_489 =>
                cases assump_488
                case inl assump_490 =>
                  apply Or.inr
                  intro assump_496
                  have assump_639 : (((p1 ∨ p1) ∧ (True → p1)) → ((False ∨ p4) ∨ (p4 → False))) := by
                    intro assump_505
                    cases assump_505
                    case intro assump_506 assump_507 =>
                      cases assump_506
                      case inl assump_508 =>
                        apply Or.inl
                        apply Or.inr
                        exact assump_496
                      case inr assump_509 =>
                        apply Or.inl
                        apply Or.inr
                        exact assump_496
                  let assump_504 := assump_2 assump_639
                  apply False.elim assump_504
                case inr assump_491 =>
                  apply Or.inr
                  intro assump_525
                  have assump_640 : (((p1 ∨ p1) ∧ (True → p1)) → ((False ∨ p4) ∨ (p4 → False))) := by
                    intro assump_534
                    cases assump_534
                    case intro assump_535 assump_536 =>
                      cases assump_535
                      case inl assump_537 =>
                        apply Or.inl
                        apply Or.inr
                        exact assump_525
                      case inr assump_538 =>
                        apply Or.inl
                        apply Or.inr
                        exact assump_525
                  let assump_533 := assump_2 assump_640
                  apply False.elim assump_533
            let assump_486 := assump_2 assump_638
            apply False.elim assump_486
          case inr assump_482 =>
            have assump_641 : (((p1 ∨ p1) ∧ (True → p1)) → ((False ∨ p4) ∨ (p4 → False))) := by
              intro assump_556
              cases assump_556
              case intro assump_557 assump_558 =>
                cases assump_557
                case inl assump_559 =>
                  apply Or.inr
                  intro assump_565
                  have assump_642 : (((p1 ∨ p1) ∧ (True → p1)) → ((False ∨ p4) ∨ (p4 → False))) := by
                    intro assump_573
                    cases assump_573
                    case intro assump_574 assump_575 =>
                      cases assump_574
                      case inl assump_576 =>
                        apply Or.inl
                        apply Or.inr
                        exact assump_565
                      case inr assump_577 =>
                        apply Or.inl
                        apply Or.inr
                        exact assump_565
                  let assump_572 := assump_2 assump_642
                  apply False.elim assump_572
                case inr assump_560 =>
                  apply Or.inr
                  intro assump_593
                  have assump_643 : (((p1 ∨ p1) ∧ (True → p1)) → ((False ∨ p4) ∨ (p4 → False))) := by
                    intro assump_601
                    cases assump_601
                    case intro assump_602 assump_603 =>
                      cases assump_602
                      case inl assump_604 =>
                        apply Or.inl
                        apply Or.inr
                        exact assump_593
                      case inr assump_605 =>
                        apply Or.inl
                        apply Or.inr
                        exact assump_593
                  let assump_600 := assump_2 assump_643
                  apply False.elim assump_600
            let assump_555 := assump_2 assump_641
            apply False.elim assump_555


variable (p5 p6 p3 p2 p0 : Prop)
theorem file92_93171 : (((((p2 ∨ p0) ∨ (p3 ∨ False)) ∨ ((p5 ∨ p3) ∨ (p6 → p6))) → False) → False) := by
  intro assump_5
  have assump_15 : (((p2 ∨ p0) ∨ (p3 ∨ False)) ∨ ((p5 ∨ p3) ∨ (p6 → p6))) := by
    apply Or.inr
    apply Or.inr
    intro assump_9
    exact assump_9
  let assump_8 := assump_5 assump_15
  apply False.elim assump_8


variable (p4 p5 p3 p0 p6 p2 : Prop)
theorem file92_93546 : (((((p0 ∧ p3) → (p4 ∧ p0)) ∧ ((False → False) ∨ (p2 ∨ False))) → (((p5 ∧ p2) ∧ (True → False)) → False)) ∨ ((((p3 ∨ p0) → (True → p6)) → ((True ∨ p2) ∨ (p5 ∨ p4))) ∧ (((p4 → False) → False) → False))) := by
  apply Or.inl
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
          have assump_39 : True := by
            apply True.intro
          let assump_23 := assump_4 assump_39
          apply False.elim assump_23
        case inr assump_18 =>
          cases assump_18
          case inl assump_27 =>
            have assump_40 : True := by
              apply True.intro
            let assump_33 := assump_4 assump_40
            apply False.elim assump_33
          case inr assump_28 =>
            apply False.elim assump_28


variable (p2 p4 : Prop)
theorem file92_94538 : ((((((p4 → False) → (p2 → True)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_17 : ((((p4 → False) → (p2 → True)) → False) → False) := by
    intro assump_5
    have assump_18 : ((p4 → False) → (p2 → True)) := by
      intro assump_9
      intro assump_10
      apply True.intro
    let assump_8 := assump_5 assump_18
    apply False.elim assump_8
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p3 p6 p2 p7 p4 p5 : Prop)
theorem file92_95039 : ((((((p7 ∨ p6) ∧ (p6 ∧ False)) ∧ ((p6 → False) → False)) → (((p2 → False) → False) → ((p5 → False) ∧ (p4 → p3)))) → False) → False) := by
  intro assump_1
  have assump_64 : ((((p7 ∨ p6) ∧ (p6 ∧ False)) ∧ ((p6 → False) → False)) → (((p2 → False) → False) → ((p5 → False) ∧ (p4 → p3)))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    intro assump_7
    cases assump_5
    case intro assump_12 assump_13 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        cases assump_14
        case inl assump_16 =>
          cases assump_15
          case intro assump_20 assump_21 =>
            apply False.elim assump_21
        case inr assump_17 =>
          cases assump_15
          case intro assump_28 assump_29 =>
            apply False.elim assump_29
    intro assump_34
    cases assump_5
    case intro assump_39 assump_40 =>
      cases assump_39
      case intro assump_41 assump_42 =>
        cases assump_41
        case inl assump_43 =>
          cases assump_42
          case intro assump_47 assump_48 =>
            apply False.elim assump_48
        case inr assump_44 =>
          cases assump_42
          case intro assump_55 assump_56 =>
            apply False.elim assump_56
  let assump_4 := assump_1 assump_64
  apply False.elim assump_4


variable (p5 p3 p1 p2 p4 p6 : Prop)
theorem file92_96395 : (((((p5 ∧ p1) ∧ (p6 ∨ False)) → ((p4 ∧ p3) → (p2 ∨ p6))) → False) → False) := by
  intro assump_1
  have assump_30 : (((p5 ∧ p1) ∧ (p6 ∨ False)) → ((p4 ∧ p3) → (p2 ∨ p6))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_5
      case intro assump_13 assump_14 =>
        cases assump_13
        case intro assump_15 assump_16 =>
          cases assump_14
          case inl assump_21 =>
            apply Or.inr
            exact assump_21
          case inr assump_22 =>
            apply False.elim assump_22
  let assump_4 := assump_1 assump_30
  apply False.elim assump_4


variable (p6 : Prop)
theorem file92_97085 : (((((True → False) ∨ (p6 → False)) → ((True ∧ False) → False)) → False) → False) := by
  intro assump_12
  have assump_27 : (((True → False) ∨ (p6 → False)) → ((True ∧ False) → False)) := by
    intro assump_16
    intro assump_17
    cases assump_17
    case intro assump_18 assump_19 =>
      apply False.elim assump_19
  let assump_15 := assump_12 assump_27
  apply False.elim assump_15


variable (p6 p3 p1 p2 p7 : Prop)
theorem file92_97532 : (((((True ∨ p7) → False) ∧ ((p2 ∧ p6) → False)) → False) ∨ ((((p1 ∧ p3) → False) → False) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_13 : (True ∨ p7) := by
      apply Or.inl
      apply True.intro
    let assump_9 := assump_2 assump_13
    apply False.elim assump_9


variable (p6 p2 p4 p3 p1 p5 p7 : Prop)
theorem file92_97934 : (((((p1 → p5) → (p3 → False)) ∧ ((p4 → p7) ∨ (True ∨ p4))) → (((True ∨ p1) ∨ (True ∧ p2)) ∨ ((True → False) ∨ (p2 ∧ p4)))) ∨ ((((p1 ∨ p1) → False) ∧ ((p6 → p3) ∨ (p3 ∧ p5))) ∧ (((p4 → p6) ∧ (p3 → p5)) → ((p4 → p4) → False)))) := by
  apply Or.inl
  intro assump_10
  cases assump_10
  case intro assump_11 assump_12 =>
    cases assump_12
    case inl assump_15 =>
      apply Or.inl
      apply Or.inl
      apply Or.inl
      apply True.intro
    case inr assump_16 =>
      cases assump_16
      case inl assump_19 =>
        apply Or.inl
        apply Or.inl
        apply Or.inl
        apply True.intro
      case inr assump_20 =>
        apply Or.inl
        apply Or.inl
        apply Or.inl
        apply True.intro


variable (p0 p2 p4 p6 p7 p5 p3 p1 : Prop)
theorem file92_98725 : (((((False ∨ p5) → False) → ((False ∨ p1) ∨ (p1 ∨ False))) → (((p4 ∧ p1) ∧ (p1 → p3)) ∧ ((True ∨ p4) ∨ (p1 ∨ p6)))) → ((((p3 ∨ p0) ∧ (p2 ∨ p7)) ∨ ((p7 ∨ p5) ∨ (p0 ∨ p4))) → (((p4 ∧ p4) → (p6 ∨ p4)) ∨ ((False ∧ p7) ∨ (p0 ∧ p4))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case inl assump_7 =>
        cases assump_6
        case inl assump_11 =>
          apply Or.inl
          intro assump_17
          cases assump_17
          case intro assump_18 assump_19 =>
            apply Or.inr
            exact assump_19
        case inr assump_12 =>
          apply Or.inl
          intro assump_28
          cases assump_28
          case intro assump_29 assump_30 =>
            apply Or.inr
            exact assump_30
      case inr assump_8 =>
        cases assump_6
        case inl assump_37 =>
          apply Or.inl
          intro assump_43
          cases assump_43
          case intro assump_44 assump_45 =>
            apply Or.inr
            exact assump_45
        case inr assump_38 =>
          apply Or.inl
          intro assump_54
          cases assump_54
          case intro assump_55 assump_56 =>
            apply Or.inr
            exact assump_56
  case inr assump_4 =>
    cases assump_4
    case inl assump_61 =>
      cases assump_61
      case inl assump_63 =>
        apply Or.inl
        intro assump_69
        cases assump_69
        case intro assump_70 assump_71 =>
          apply Or.inr
          exact assump_71
      case inr assump_64 =>
        apply Or.inl
        intro assump_80
        cases assump_80
        case intro assump_81 assump_82 =>
          apply Or.inr
          exact assump_82
    case inr assump_62 =>
      cases assump_62
      case inl assump_87 =>
        apply Or.inl
        intro assump_93
        cases assump_93
        case intro assump_94 assump_95 =>
          apply Or.inr
          exact assump_95
      case inr assump_88 =>
        apply Or.inl
        intro assump_104
        cases assump_104
        case intro assump_105 assump_106 =>
          apply Or.inr
          exact assump_106


variable (p2 p1 p6 p7 p4 p3 p0 : Prop)
theorem file92_100977 : ((((((p7 → False) ∨ (p0 ∨ p1)) → ((p3 ∧ p0) → (True ∨ p2))) → (((p7 ∧ False) → (p0 → p1)) ∨ ((p1 → False) ∨ (p4 ∧ p6)))) → False) → False) := by
  intro assump_1
  have assump_21 : ((((p7 → False) ∨ (p0 ∨ p1)) → ((p3 ∧ p0) → (True ∨ p2))) → (((p7 ∧ False) → (p0 → p1)) ∨ ((p1 → False) ∨ (p4 ∧ p6)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    intro assump_9
    cases assump_8
    case intro assump_12 assump_13 =>
      apply False.elim assump_13
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p1 p0 p6 p3 p2 p4 : Prop)
theorem file92_101572 : (((((p1 → False) → False) ∧ ((p1 → False) ∧ (p6 ∨ p3))) → False) ∨ ((((False → p0) ∧ (p6 ∧ p2)) → False) ∧ (((False → p4) → False) ∨ ((p2 ∨ False) → False)))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        have assump_46 : (p1 → False) := by
          intro assump_17
          have assump_47 : p1 := by
            exact assump_17
          let assump_22 := assump_6 assump_47
          apply False.elim assump_22
        let assump_16 := assump_2 assump_46
        apply False.elim assump_16
      case inr assump_11 =>
        have assump_48 : (p1 → False) := by
          intro assump_34
          have assump_49 : p1 := by
            exact assump_34
          let assump_39 := assump_6 assump_49
          apply False.elim assump_39
        let assump_33 := assump_2 assump_48
        apply False.elim assump_33


