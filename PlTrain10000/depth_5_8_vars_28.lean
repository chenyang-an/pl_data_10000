variable (p4 p7 p0 p2 p3 p6 : Prop)
theorem file28_44 : ((((((False ∨ p3) → False) → ((False → p4) ∨ (p0 → p7))) → False) ∨ ((((p6 → False) ∨ (p7 ∨ p7)) → ((p6 ∧ False) → (False ∧ p2))) → False)) → False) := by
  intro assump_22
  cases assump_22
  case inl assump_23 =>
    have assump_57 : (((False ∨ p3) → False) → ((False → p4) ∨ (p0 → p7))) := by
      intro assump_28
      apply Or.inl
      intro assump_31
      apply False.elim assump_31
    let assump_27 := assump_23 assump_57
    apply False.elim assump_27
  case inr assump_24 =>
    have assump_58 : (((p6 → False) ∨ (p7 ∨ p7)) → ((p6 ∧ False) → (False ∧ p2))) := by
      intro assump_40
      intro assump_41
      apply And.intro
      cases assump_41
      case intro assump_42 assump_43 =>
        apply False.elim assump_43
      cases assump_41
      case intro assump_48 assump_49 =>
        apply False.elim assump_49
    let assump_39 := assump_24 assump_58
    apply False.elim assump_39


variable (p4 p3 p7 p0 : Prop)
theorem file28_1006 : (((((p7 ∨ True) ∨ (p0 ∨ p4)) → False) ∨ (((p3 ∧ p3) → (False → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_20 : ((p7 ∨ True) ∨ (p0 ∨ p4)) := by
      apply Or.inl
      apply Or.inr
      apply True.intro
    let assump_6 := assump_2 assump_20
    apply False.elim assump_6
  case inr assump_3 =>
    have assump_21 : ((p3 ∧ p3) → (False → False)) := by
      intro assump_13
      intro assump_14
      apply False.elim assump_14
    let assump_12 := assump_3 assump_21
    apply False.elim assump_12


variable (p3 p7 p1 p4 p0 p2 p6 : Prop)
theorem file28_1633 : (((((p7 → False) → (p7 → False)) ∨ ((p3 → p0) ∨ (p7 ∧ True))) → False) → ((((p7 → p4) ∨ (p2 → False)) → ((p3 → False) → False)) → (((p1 ∨ p2) ∨ (p4 → False)) → ((p6 ∧ p3) → (p1 → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  intro assump_5
  cases assump_4
  case intro assump_8 assump_9 =>
    cases assump_3
    case inl assump_14 =>
      cases assump_14
      case inl assump_16 =>
        have assump_78 : (((p7 → False) → (p7 → False)) ∨ ((p3 → p0) ∨ (p7 ∧ True))) := by
          apply Or.inl
          intro assump_25
          intro assump_26
          have assump_79 : p7 := by
            exact assump_26
          let assump_31 := assump_25 assump_79
          apply False.elim assump_31
        let assump_24 := assump_1 assump_78
        apply False.elim assump_24
      case inr assump_17 =>
        have assump_80 : (((p7 → False) → (p7 → False)) ∨ ((p3 → p0) ∨ (p7 ∧ True))) := by
          apply Or.inl
          intro assump_45
          intro assump_46
          have assump_81 : p7 := by
            exact assump_46
          let assump_51 := assump_45 assump_81
          apply False.elim assump_51
        let assump_44 := assump_1 assump_80
        apply False.elim assump_44
    case inr assump_15 =>
      have assump_82 : (((p7 → False) → (p7 → False)) ∨ ((p3 → p0) ∨ (p7 ∧ True))) := by
        apply Or.inl
        intro assump_65
        intro assump_66
        have assump_83 : p7 := by
          exact assump_66
        let assump_71 := assump_65 assump_83
        apply False.elim assump_71
      let assump_64 := assump_1 assump_82
      apply False.elim assump_64


variable (p1 p4 p5 : Prop)
theorem file28_3324 : (((((p5 ∧ p4) → False) → False) ∧ (((p1 → False) ∧ (p1 ∧ p5)) ∧ ((p1 ∧ p5) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          have assump_24 : (p1 ∧ p5) := by
            apply And.intro
            exact assump_12
            exact assump_13
          let assump_20 := assump_7 assump_24
          apply False.elim assump_20


variable (p3 p5 p6 p4 : Prop)
theorem file28_3936 : ((((((p5 ∧ p4) → False) ∧ ((True → False) ∨ (True → False))) → False) ∧ ((((p5 → False) → (False → p3)) ∨ ((p6 → True) → False)) → (((False ∧ True) → False) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_22 : (((p5 → False) → (False → p3)) ∨ ((p6 → True) → False)) := by
      apply Or.inl
      intro assump_9
      intro assump_10
      apply False.elim assump_10
    let assump_8 := assump_3 assump_22
    have assump_23 : ((False ∧ True) → False) := by
      intro assump_14
      cases assump_14
      case intro assump_15 assump_16 =>
        apply False.elim assump_15
    let assump_13 := assump_8 assump_23
    apply False.elim assump_13


variable (p6 p0 p5 p3 : Prop)
theorem file28_4700 : (((((p6 ∧ p3) ∧ (True → False)) ∧ ((p6 → p5) ∧ (p6 → False))) → False) ∨ ((((p5 → p5) → False) ∨ ((True ∨ p5) ∧ (p6 ∨ p0))) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_3
        case intro assump_14 assump_15 =>
          have assump_24 : p6 := by
            exact assump_6
          let assump_20 := assump_15 assump_24
          apply False.elim assump_20


variable (p0 p4 p1 p7 p6 p3 : Prop)
theorem file28_5309 : (((((False → False) → (p3 ∧ False)) ∧ ((p3 ∨ p4) ∧ (False → p1))) → False) ∨ ((((p0 → False) → (True → True)) → ((p6 → False) → (p0 → p0))) ∧ (((p7 → False) ∨ (p4 ∨ True)) ∨ ((False → False) ∨ (p3 → False))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        have assump_40 : (False → False) := by
          intro assump_17
          apply False.elim assump_17
        let assump_16 := assump_2 assump_40
        let assump_20 := And.right assump_16
        apply False.elim assump_20
      case inr assump_9 =>
        have assump_41 : (False → False) := by
          intro assump_32
          apply False.elim assump_32
        let assump_31 := assump_2 assump_41
        let assump_35 := And.right assump_31
        apply False.elim assump_35


variable (p7 p2 p0 p1 p3 p5 p4 : Prop)
theorem file28_6269 : (((((True → p0) ∧ (p7 → False)) ∧ ((p7 ∧ p1) ∧ (False → False))) ∨ (((p0 → True) ∨ (p5 → p3)) → False)) → ((((p5 → p4) ∧ (p0 → p0)) → False) ∨ (((p7 ∨ p0) → (p2 → False)) → False))) := by
  intro assump_5
  cases assump_5
  case inl assump_6 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        cases assump_9
        case intro assump_16 assump_17 =>
          cases assump_16
          case intro assump_18 assump_19 =>
            apply Or.inl
            intro assump_26
            cases assump_26
            case intro assump_27 assump_28 =>
              have assump_58 : p7 := by
                exact assump_18
              let assump_38 := assump_11 assump_58
              apply False.elim assump_38
  case inr assump_7 =>
    apply Or.inl
    intro assump_44
    cases assump_44
    case intro assump_45 assump_46 =>
      have assump_59 : ((p0 → True) ∨ (p5 → p3)) := by
        apply Or.inl
        intro assump_54
        apply True.intro
      let assump_53 := assump_7 assump_59
      apply False.elim assump_53


variable (p7 p0 p5 p3 : Prop)
theorem file28_7428 : (((((p0 ∨ p5) ∧ (p3 → p7)) → ((False → p0) ∧ (False → False))) → False) → False) := by
  intro assump_1
  have assump_15 : (((p0 ∨ p5) ∧ (p3 → p7)) → ((False → p0) ∧ (False → False))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    apply False.elim assump_6
    intro assump_9
    apply False.elim assump_9
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p7 p0 p2 p1 p4 p3 : Prop)
theorem file28_7880 : (((((True → False) → False) ∧ ((p0 → p1) ∧ (False ∧ p7))) → False) ∨ ((((p2 ∧ p0) ∨ (p4 → p7)) ∧ ((p4 ∧ p3) → (p0 ∧ p0))) ∧ (((p4 → p3) → False) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        apply False.elim assump_10


variable (p7 p3 p0 p4 : Prop)
theorem file28_8330 : ((((((False → p7) ∨ (p0 → p4)) → False) → False) → ((((p3 ∧ p7) ∧ (True → False)) → False) → False)) → False) := by
  intro assump_1
  have assump_34 : ((((False → p7) ∨ (p0 → p4)) → False) → False) := by
    intro assump_5
    have assump_35 : ((False → p7) ∨ (p0 → p4)) := by
      apply Or.inl
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_35
    apply False.elim assump_8
  let assump_4 := assump_1 assump_34
  have assump_36 : (((p3 ∧ p7) ∧ (True → False)) → False) := by
    intro assump_16
    cases assump_16
    case intro assump_17 assump_18 =>
      cases assump_17
      case intro assump_19 assump_20 =>
        have assump_37 : True := by
          apply True.intro
        let assump_27 := assump_18 assump_37
        apply False.elim assump_27
  let assump_15 := assump_4 assump_36
  apply False.elim assump_15


variable (p7 p0 p3 p6 p5 : Prop)
theorem file28_9257 : ((((((p6 ∨ p3) ∧ (p7 ∨ p5)) → False) → (((p3 ∧ p3) ∧ (p0 ∧ p5)) → False)) → False) → False) := by
  intro assump_1
  have assump_30 : ((((p6 ∨ p3) ∧ (p7 ∨ p5)) → False) → (((p3 ∧ p3) ∧ (p0 ∧ p5)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_8
        case intro assump_15 assump_16 =>
          have assump_31 : ((p6 ∨ p3) ∧ (p7 ∨ p5)) := by
            apply And.intro
            apply Or.inr
            exact assump_10
            apply Or.inr
            exact assump_16
          let assump_23 := assump_5 assump_31
          apply False.elim assump_23
  let assump_4 := assump_1 assump_30
  apply False.elim assump_4


variable (p0 p5 p6 p2 p1 p3 : Prop)
theorem file28_10086 : (((((p0 ∨ False) ∧ (p2 → False)) → ((p1 → True) ∨ (p3 → False))) → False) → ((((p0 ∧ p5) ∨ (p6 → False)) → False) → False)) := by
  intro assump_1
  intro assump_2
  have assump_23 : (((p0 ∨ False) ∧ (p2 → False)) → ((p1 → True) ∨ (p3 → False))) := by
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        apply Or.inl
        intro assump_17
        apply True.intro
      case inr assump_12 =>
        apply False.elim assump_12
  let assump_7 := assump_1 assump_23
  apply False.elim assump_7


variable (p7 p6 p0 p4 p2 : Prop)
theorem file28_10717 : ((((((p0 ∧ p2) ∨ (False → False)) → False) → (((p6 → p4) ∨ (p0 → False)) ∨ ((True → p7) ∧ (p2 ∧ p7)))) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p0 ∧ p2) ∨ (False → False)) → False) → (((p6 → p4) ∨ (p0 → False)) ∨ ((True → p7) ∧ (p2 ∧ p7)))) := by
    intro assump_5
    apply Or.inl
    apply Or.inl
    intro assump_8
    have assump_23 : ((p0 ∧ p2) ∨ (False → False)) := by
      apply Or.inr
      intro assump_13
      apply False.elim assump_13
    let assump_12 := assump_5 assump_23
    apply False.elim assump_12
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p2 p4 p6 p0 p3 p7 p1 : Prop)
theorem file28_11389 : ((((((p0 → False) → False) → False) → False) ∧ ((((False ∧ False) ∧ (True → p4)) ∨ ((p1 → p7) ∨ (p2 → p3))) ∧ (((False → True) → (True → False)) ∧ ((False → True) → (p6 ∧ p2))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            apply False.elim assump_12
      case inr assump_9 =>
        cases assump_9
        case inl assump_16 =>
          cases assump_7
          case intro assump_20 assump_21 =>
            have assump_56 : (False → True) := by
              intro assump_32
              apply True.intro
            let assump_31 := assump_20 assump_56
            have assump_57 : True := by
              apply True.intro
            let assump_33 := assump_31 assump_57
            apply False.elim assump_33
        case inr assump_17 =>
          cases assump_7
          case intro assump_39 assump_40 =>
            have assump_58 : (False → True) := by
              intro assump_51
              apply True.intro
            let assump_50 := assump_39 assump_58
            have assump_59 : True := by
              apply True.intro
            let assump_52 := assump_50 assump_59
            apply False.elim assump_52


variable (p7 p2 p3 p4 p0 p1 p6 p5 : Prop)
theorem file28_12880 : (((((p1 ∧ p1) ∨ (p7 → True)) → ((True → p5) → False)) ∧ (((p1 ∧ p0) ∧ (p2 → p1)) ∧ ((True ∨ p7) ∧ (True → False)))) → ((((p4 ∧ p7) ∨ (p7 → p3)) → ((p6 ∨ True) ∧ (p3 ∨ p1))) ∨ (((p3 ∧ p3) ∧ (p4 ∧ p1)) ∨ ((p4 ∧ p2) ∧ (p3 → False))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_7
          case intro assump_18 assump_19 =>
            cases assump_18
            case inl assump_20 =>
              apply Or.inl
              intro assump_26
              apply And.intro
              cases assump_26
              case inl assump_27 =>
                cases assump_27
                case intro assump_29 assump_30 =>
                  apply Or.inr
                  apply True.intro
              case inr assump_28 =>
                apply Or.inr
                apply True.intro
              cases assump_26
              case inl assump_37 =>
                cases assump_37
                case intro assump_39 assump_40 =>
                  apply Or.inr
                  exact assump_10
              case inr assump_38 =>
                apply Or.inr
                exact assump_10
            case inr assump_21 =>
              apply Or.inl
              intro assump_51
              apply And.intro
              cases assump_51
              case inl assump_52 =>
                cases assump_52
                case intro assump_54 assump_55 =>
                  apply Or.inr
                  apply True.intro
              case inr assump_53 =>
                apply Or.inr
                apply True.intro
              cases assump_51
              case inl assump_62 =>
                cases assump_62
                case intro assump_64 assump_65 =>
                  apply Or.inr
                  exact assump_10
              case inr assump_63 =>
                apply Or.inr
                exact assump_10


variable (p6 p1 p5 p3 p4 p7 p2 : Prop)
theorem file28_15011 : (((((p4 → p6) ∧ (p4 ∧ p7)) → False) → (((p7 ∧ p1) → False) → ((p3 → False) ∨ (p5 → p5)))) → ((((p5 → False) ∧ (p2 ∧ False)) ∧ ((p6 → p1) ∧ (p6 → False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_6
      case intro assump_9 assump_10 =>
        apply False.elim assump_10


variable (p4 p0 p5 p3 p7 p1 p2 p6 : Prop)
theorem file28_15482 : (((((p7 → p6) ∨ (p1 ∨ p5)) → ((p3 → p6) → False)) ∧ (((p0 → False) ∨ (p3 → False)) ∨ ((p2 → p4) ∨ (p2 → False)))) → ((((p2 ∧ False) ∧ (p0 → p6)) → ((p2 ∨ p2) → False)) ∧ (((p4 → False) → False) → ((p7 → p1) → (p6 → True))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_2
    case intro assump_8 assump_9 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        apply False.elim assump_11
  case inr assump_5 =>
    cases assump_2
    case intro assump_18 assump_19 =>
      cases assump_18
      case intro assump_20 assump_21 =>
        apply False.elim assump_21
  intro assump_26
  intro assump_27
  intro assump_28
  apply True.intro


variable (p3 p4 p5 p6 p7 p2 p0 p1 : Prop)
theorem file28_16289 : ((((((False ∧ p7) → False) → ((p5 → False) ∧ (True → p3))) ∧ (((p2 ∨ False) → False) ∨ ((False → False) ∧ (p1 ∨ p5)))) ∧ ((((p4 → p4) ∨ (p5 ∨ p0)) ∧ ((p1 ∧ False) ∧ (True ∧ p6))) ∧ (((p5 ∨ p1) → (p7 → p6)) → ((p2 → False) ∧ (p0 → p4))))) → False) := by
  intro assump_14
  cases assump_14
  case intro assump_15 assump_16 =>
    cases assump_15
    case intro assump_17 assump_18 =>
      cases assump_18
      case inl assump_21 =>
        cases assump_16
        case intro assump_25 assump_26 =>
          cases assump_25
          case intro assump_27 assump_28 =>
            cases assump_27
            case inl assump_29 =>
              cases assump_28
              case intro assump_33 assump_34 =>
                cases assump_33
                case intro assump_35 assump_36 =>
                  apply False.elim assump_36
            case inr assump_30 =>
              cases assump_30
              case inl assump_41 =>
                cases assump_28
                case intro assump_45 assump_46 =>
                  cases assump_45
                  case intro assump_47 assump_48 =>
                    apply False.elim assump_48
              case inr assump_42 =>
                cases assump_28
                case intro assump_55 assump_56 =>
                  cases assump_55
                  case intro assump_57 assump_58 =>
                    apply False.elim assump_58
      case inr assump_22 =>
        cases assump_22
        case intro assump_63 assump_64 =>
          cases assump_64
          case inl assump_67 =>
            cases assump_16
            case intro assump_71 assump_72 =>
              cases assump_71
              case intro assump_73 assump_74 =>
                cases assump_73
                case inl assump_75 =>
                  cases assump_74
                  case intro assump_79 assump_80 =>
                    cases assump_79
                    case intro assump_81 assump_82 =>
                      apply False.elim assump_82
                case inr assump_76 =>
                  cases assump_76
                  case inl assump_87 =>
                    cases assump_74
                    case intro assump_91 assump_92 =>
                      cases assump_91
                      case intro assump_93 assump_94 =>
                        apply False.elim assump_94
                  case inr assump_88 =>
                    cases assump_74
                    case intro assump_101 assump_102 =>
                      cases assump_101
                      case intro assump_103 assump_104 =>
                        apply False.elim assump_104
          case inr assump_68 =>
            cases assump_16
            case intro assump_111 assump_112 =>
              cases assump_111
              case intro assump_113 assump_114 =>
                cases assump_113
                case inl assump_115 =>
                  cases assump_114
                  case intro assump_119 assump_120 =>
                    cases assump_119
                    case intro assump_121 assump_122 =>
                      apply False.elim assump_122
                case inr assump_116 =>
                  cases assump_116
                  case inl assump_127 =>
                    cases assump_114
                    case intro assump_131 assump_132 =>
                      cases assump_131
                      case intro assump_133 assump_134 =>
                        apply False.elim assump_134
                  case inr assump_128 =>
                    cases assump_114
                    case intro assump_141 assump_142 =>
                      cases assump_141
                      case intro assump_143 assump_144 =>
                        apply False.elim assump_144


variable (p5 p3 p4 p2 p6 : Prop)
theorem file28_20108 : (((((p3 → False) → False) ∧ ((p6 ∨ False) ∧ (p6 → False))) → False) ∨ ((((p5 → True) ∨ (p5 ∨ False)) ∨ ((p2 → False) → False)) ∨ (((p4 → False) → False) ∨ ((False → False) → (False ∨ p3))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        have assump_20 : p6 := by
          exact assump_8
        let assump_14 := assump_7 assump_20
        apply False.elim assump_14
      case inr assump_9 =>
        apply False.elim assump_9


variable (p0 p6 p1 p3 p5 p7 p4 p2 : Prop)
theorem file28_20756 : (((((p3 ∧ False) ∨ (p4 → False)) ∨ ((p2 ∨ p7) → False)) ∧ (((p5 ∧ p2) → False) ∨ ((p4 → False) → False))) → ((((p3 ∨ False) ∧ (p3 → False)) ∨ ((p4 ∧ p6) ∨ (p2 → p2))) → (((True → p3) → (False → False)) ∨ ((p0 ∧ p6) ∧ (p1 ∨ False))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case inl assump_7 =>
        cases assump_1
        case intro assump_13 assump_14 =>
          cases assump_13
          case inl assump_15 =>
            cases assump_15
            case inl assump_17 =>
              cases assump_17
              case intro assump_19 assump_20 =>
                apply False.elim assump_20
            case inr assump_18 =>
              cases assump_14
              case inl assump_27 =>
                apply Or.inl
                intro assump_31
                intro assump_32
                apply False.elim assump_32
              case inr assump_28 =>
                apply Or.inl
                intro assump_37
                intro assump_38
                apply False.elim assump_38
          case inr assump_16 =>
            cases assump_14
            case inl assump_43 =>
              apply Or.inl
              intro assump_47
              intro assump_48
              apply False.elim assump_48
            case inr assump_44 =>
              apply Or.inl
              intro assump_53
              intro assump_54
              apply False.elim assump_54
      case inr assump_8 =>
        apply False.elim assump_8
  case inr assump_4 =>
    cases assump_4
    case inl assump_59 =>
      cases assump_59
      case intro assump_61 assump_62 =>
        cases assump_1
        case intro assump_67 assump_68 =>
          cases assump_67
          case inl assump_69 =>
            cases assump_69
            case inl assump_71 =>
              cases assump_71
              case intro assump_73 assump_74 =>
                apply False.elim assump_74
            case inr assump_72 =>
              cases assump_68
              case inl assump_81 =>
                apply Or.inl
                intro assump_85
                intro assump_86
                apply False.elim assump_86
              case inr assump_82 =>
                apply Or.inl
                intro assump_91
                intro assump_92
                apply False.elim assump_92
          case inr assump_70 =>
            cases assump_68
            case inl assump_97 =>
              apply Or.inl
              intro assump_101
              intro assump_102
              apply False.elim assump_102
            case inr assump_98 =>
              apply Or.inl
              intro assump_107
              intro assump_108
              apply False.elim assump_108
    case inr assump_60 =>
      cases assump_1
      case intro assump_113 assump_114 =>
        cases assump_113
        case inl assump_115 =>
          cases assump_115
          case inl assump_117 =>
            cases assump_117
            case intro assump_119 assump_120 =>
              apply False.elim assump_120
          case inr assump_118 =>
            cases assump_114
            case inl assump_127 =>
              apply Or.inl
              intro assump_131
              intro assump_132
              apply False.elim assump_132
            case inr assump_128 =>
              apply Or.inl
              intro assump_137
              intro assump_138
              apply False.elim assump_138
        case inr assump_116 =>
          cases assump_114
          case inl assump_143 =>
            apply Or.inl
            intro assump_147
            intro assump_148
            apply False.elim assump_148
          case inr assump_144 =>
            apply Or.inl
            intro assump_153
            intro assump_154
            apply False.elim assump_154


variable (p3 p0 p1 p2 p7 p5 : Prop)
theorem file28_24714 : ((((((p1 ∨ p7) ∨ (p5 ∧ p3)) → ((False → False) ∧ (True ∨ p0))) → False) ∨ ((((p7 → p7) → (False ∧ False)) → ((p2 → False) → (True ∧ p7))) → False)) → False) := by
  intro assump_12
  cases assump_12
  case inl assump_13 =>
    have assump_59 : (((p1 ∨ p7) ∨ (p5 ∧ p3)) → ((False → False) ∧ (True ∨ p0))) := by
      intro assump_18
      apply And.intro
      intro assump_19
      apply False.elim assump_19
      cases assump_18
      case inl assump_22 =>
        cases assump_22
        case inl assump_24 =>
          apply Or.inl
          apply True.intro
        case inr assump_25 =>
          apply Or.inl
          apply True.intro
      case inr assump_23 =>
        cases assump_23
        case intro assump_30 assump_31 =>
          apply Or.inl
          apply True.intro
    let assump_17 := assump_13 assump_59
    apply False.elim assump_17
  case inr assump_14 =>
    have assump_60 : (((p7 → p7) → (False ∧ False)) → ((p2 → False) → (True ∧ p7))) := by
      intro assump_42
      intro assump_43
      apply And.intro
      apply True.intro
      have assump_61 : (p7 → p7) := by
        intro assump_49
        exact assump_49
      let assump_48 := assump_42 assump_61
      let assump_52 := And.left assump_48
      apply False.elim assump_52
    let assump_41 := assump_14 assump_60
    apply False.elim assump_41


variable (p7 p3 p4 p2 p0 p1 : Prop)
theorem file28_26113 : ((((((True ∧ p3) ∨ (p4 ∧ False)) → ((p1 → p2) → False)) → (((p2 ∧ p0) ∧ (p3 ∧ p7)) → False)) → False) → False) := by
  intro assump_13
  have assump_46 : ((((True ∧ p3) ∨ (p4 ∧ False)) → ((p1 → p2) → False)) → (((p2 ∧ p0) ∧ (p3 ∧ p7)) → False)) := by
    intro assump_17
    intro assump_18
    cases assump_18
    case intro assump_19 assump_20 =>
      cases assump_19
      case intro assump_21 assump_22 =>
        cases assump_20
        case intro assump_27 assump_28 =>
          have assump_47 : ((True ∧ p3) ∨ (p4 ∧ False)) := by
            apply Or.inl
            apply And.intro
            apply True.intro
            exact assump_27
          let assump_35 := assump_17 assump_47
          have assump_48 : (p1 → p2) := by
            intro assump_37
            exact assump_21
          let assump_36 := assump_35 assump_48
          apply False.elim assump_36
  let assump_16 := assump_13 assump_46
  apply False.elim assump_16


variable (p1 p7 p5 p3 p2 p6 : Prop)
theorem file28_27120 : (((((False → False) → False) → False) ∨ (((p7 ∨ p2) → False) → False)) ∨ ((((p2 → False) ∨ (p5 ∨ p3)) → ((p6 ∨ p1) ∧ (False ∧ True))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_5
  have assump_15 : (False → False) := by
    intro assump_9
    apply False.elim assump_9
  let assump_8 := assump_5 assump_15
  apply False.elim assump_8


variable (p5 p2 p4 p3 p7 : Prop)
theorem file28_27529 : ((((((True → False) → (p4 → False)) → False) → (((p7 ∧ p7) ∧ (p5 ∧ p4)) ∧ ((p3 → p2) ∨ (p7 ∧ p3)))) → False) → False) := by
  intro assump_1
  have assump_93 : ((((True → False) → (p4 → False)) → False) → (((p7 ∧ p7) ∧ (p5 ∧ p4)) ∧ ((p3 → p2) ∨ (p7 ∧ p3)))) := by
    intro assump_5
    apply And.intro
    apply And.intro
    apply And.intro
    have assump_94 : ((True → False) → (p4 → False)) := by
      intro assump_9
      intro assump_10
      have assump_95 : True := by
        apply True.intro
      let assump_15 := assump_9 assump_95
      apply False.elim assump_15
    let assump_8 := assump_5 assump_94
    apply False.elim assump_8
    have assump_96 : ((True → False) → (p4 → False)) := by
      intro assump_25
      intro assump_26
      have assump_97 : True := by
        apply True.intro
      let assump_31 := assump_25 assump_97
      apply False.elim assump_31
    let assump_24 := assump_5 assump_96
    apply False.elim assump_24
    apply And.intro
    have assump_98 : ((True → False) → (p4 → False)) := by
      intro assump_41
      intro assump_42
      have assump_99 : True := by
        apply True.intro
      let assump_47 := assump_41 assump_99
      apply False.elim assump_47
    let assump_40 := assump_5 assump_98
    apply False.elim assump_40
    have assump_100 : ((True → False) → (p4 → False)) := by
      intro assump_57
      intro assump_58
      have assump_101 : True := by
        apply True.intro
      let assump_63 := assump_57 assump_101
      apply False.elim assump_63
    let assump_56 := assump_5 assump_100
    apply False.elim assump_56
    apply Or.inl
    intro assump_72
    have assump_102 : ((True → False) → (p4 → False)) := by
      intro assump_77
      intro assump_78
      have assump_103 : True := by
        apply True.intro
      let assump_83 := assump_77 assump_103
      apply False.elim assump_83
    let assump_76 := assump_5 assump_102
    apply False.elim assump_76
  let assump_4 := assump_1 assump_93
  apply False.elim assump_4


variable (p1 p6 p5 p7 : Prop)
theorem file28_29597 : (((((True ∨ False) → (p1 → False)) ∧ ((p5 ∨ p1) ∧ (p7 ∧ False))) ∧ (((p1 ∨ p6) ∨ (False → p1)) → False)) → False) := by
  intro assump_21
  cases assump_21
  case intro assump_22 assump_23 =>
    cases assump_22
    case intro assump_24 assump_25 =>
      cases assump_25
      case intro assump_28 assump_29 =>
        cases assump_28
        case inl assump_30 =>
          cases assump_29
          case intro assump_34 assump_35 =>
            apply False.elim assump_35
        case inr assump_31 =>
          cases assump_29
          case intro assump_42 assump_43 =>
            apply False.elim assump_43


variable (p0 p2 p3 p4 p1 : Prop)
theorem file28_30268 : ((((((p0 ∧ p4) ∨ (p1 ∧ p0)) ∨ ((p0 ∨ True) ∨ (True ∧ p1))) ∨ (((p2 ∨ p4) → False) ∧ ((p3 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_8 : ((((p0 ∧ p4) ∨ (p1 ∧ p0)) ∨ ((p0 ∨ True) ∨ (True ∧ p1))) ∨ (((p2 ∨ p4) → False) ∧ ((p3 → False) → False))) := by
    apply Or.inl
    apply Or.inr
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p6 p3 p7 p0 : Prop)
theorem file28_30756 : (((((p0 ∨ p3) → False) → ((p7 ∧ p0) → (False → p6))) → False) → False) := by
  intro assump_20
  have assump_32 : (((p0 ∨ p3) → False) → ((p7 ∧ p0) → (False → p6))) := by
    intro assump_24
    intro assump_25
    intro assump_26
    apply False.elim assump_26
  let assump_23 := assump_20 assump_32
  apply False.elim assump_23


variable (p5 p0 p2 p7 p3 p6 : Prop)
theorem file28_31146 : (((((p6 ∧ p0) ∧ (p2 ∨ p3)) → ((p0 → False) → (p2 → False))) ∨ (((True → False) ∧ (True ∧ p2)) → False)) ∧ ((((p3 → False) → (p3 → False)) ∨ ((p5 → p3) → False)) ∨ (((p5 → p7) ∧ (False → p7)) → False))) := by
  apply And.intro
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_1
  case intro assump_8 assump_9 =>
    cases assump_8
    case intro assump_10 assump_11 =>
      cases assump_9
      case inl assump_16 =>
        have assump_46 : p0 := by
          exact assump_11
        let assump_23 := assump_2 assump_46
        apply False.elim assump_23
      case inr assump_17 =>
        have assump_47 : p0 := by
          exact assump_11
        let assump_32 := assump_2 assump_47
        apply False.elim assump_32
  apply Or.inl
  apply Or.inl
  intro assump_36
  intro assump_37
  have assump_48 : p3 := by
    exact assump_37
  let assump_42 := assump_36 assump_48
  apply False.elim assump_42


variable (p5 p3 p4 p1 p6 p0 p7 p2 : Prop)
theorem file28_32149 : (((((p6 ∨ p2) → (p1 ∧ p5)) ∧ ((True → False) ∧ (False ∧ p4))) → (((p2 ∨ p2) → False) ∧ ((p6 → p5) ∨ (p4 → p0)))) ∨ ((((p6 → True) → False) ∨ ((p3 ∨ True) → (p7 ∧ False))) ∧ (((p4 ∧ p4) ∧ (True ∧ p5)) → False))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        cases assump_12
        case intro assump_15 assump_16 =>
          apply False.elim assump_15
  case inr assump_4 =>
    cases assump_1
    case intro assump_21 assump_22 =>
      cases assump_22
      case intro assump_25 assump_26 =>
        cases assump_26
        case intro assump_29 assump_30 =>
          apply False.elim assump_29
  cases assump_1
  case intro assump_33 assump_34 =>
    cases assump_34
    case intro assump_37 assump_38 =>
      cases assump_38
      case intro assump_41 assump_42 =>
        apply False.elim assump_41


variable (p6 p4 p3 p1 p5 p7 p0 p2 : Prop)
theorem file28_33211 : (((((p1 ∧ p5) ∨ (True ∨ p0)) ∨ ((p1 ∨ p6) → False)) → (((p5 ∧ False) ∧ (p4 → False)) → False)) ∨ ((((p7 ∧ p6) ∨ (p3 ∨ False)) → False) ∧ (((True → False) → False) ∧ ((p3 ∨ p2) ∨ (p0 → False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      apply False.elim assump_6


variable (p0 p7 p5 p1 p3 : Prop)
theorem file28_33656 : ((((((p0 → p0) → False) ∧ ((True → p3) ∧ (True → False))) → (((p3 → False) ∧ (p1 ∨ True)) → ((True ∧ p0) → (p7 → p5)))) → False) → False) := by
  intro assump_25
  have assump_82 : ((((p0 → p0) → False) ∧ ((True → p3) ∧ (True → False))) → (((p3 → False) ∧ (p1 ∨ True)) → ((True ∧ p0) → (p7 → p5)))) := by
    intro assump_29
    intro assump_30
    intro assump_31
    intro assump_32
    cases assump_31
    case intro assump_35 assump_36 =>
      cases assump_30
      case intro assump_41 assump_42 =>
        cases assump_42
        case inl assump_45 =>
          cases assump_29
          case intro assump_49 assump_50 =>
            cases assump_50
            case intro assump_53 assump_54 =>
              have assump_83 : True := by
                apply True.intro
              let assump_59 := assump_54 assump_83
              apply False.elim assump_59
        case inr assump_46 =>
          cases assump_29
          case intro assump_65 assump_66 =>
            cases assump_66
            case intro assump_69 assump_70 =>
              have assump_84 : True := by
                apply True.intro
              let assump_75 := assump_70 assump_84
              apply False.elim assump_75
  let assump_28 := assump_25 assump_82
  apply False.elim assump_28


variable (p6 p4 p1 p2 p3 p5 : Prop)
theorem file28_34995 : (((((p2 ∧ p6) ∧ (True ∨ True)) → False) ∨ (((p5 → p5) → (p4 → p4)) → ((p6 → p4) ∨ (p2 → p3)))) → ((((True → p1) → False) → False) → (((True ∧ p6) ∨ (p1 ∧ p6)) ∨ ((False ∧ p1) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    apply Or.inr
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      apply False.elim assump_10
  case inr assump_6 =>
    apply Or.inr
    intro assump_16
    cases assump_16
    case intro assump_17 assump_18 =>
      apply False.elim assump_17


variable (p0 p2 p7 p3 p1 p5 p4 p6 : Prop)
theorem file28_35605 : (((((p6 → False) ∨ (p7 ∧ p0)) → ((p3 ∨ True) ∨ (p7 → False))) ∨ (((True → p3) → False) ∨ ((p5 → False) ∨ (p6 ∨ False)))) ∨ ((((True → False) → (p2 ∧ False)) → ((p4 ∧ p1) ∧ (p0 ∨ p7))) ∨ (((p6 → p1) → (p7 ∧ p3)) → ((p1 → False) → (p7 → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply Or.inr
    apply True.intro
  case inr assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      apply Or.inl
      apply Or.inr
      apply True.intro


variable (p0 p7 p2 : Prop)
theorem file28_36189 : ((((((True ∨ p0) → False) → False) ∨ (((p0 → False) ∨ (p2 → False)) → ((p7 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((True ∨ p0) → False) → False) ∨ (((p0 → False) ∨ (p2 → False)) → ((p7 → False) → False))) := by
    apply Or.inl
    intro assump_5
    have assump_16 : (True ∨ p0) := by
      apply Or.inl
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p0 p3 p2 p4 p1 p6 p7 : Prop)
theorem file28_36757 : ((((((p7 ∧ False) → False) ∨ ((p0 → False) ∧ (p2 → p1))) ∨ (((False → False) → False) ∨ ((p3 ∨ p6) → (p7 ∨ p7)))) ∧ ((((p7 ∨ p1) ∨ (p2 ∧ p1)) ∨ ((p6 ∧ p1) → (p4 ∨ p3))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        have assump_98 : (((p7 ∨ p1) ∨ (p2 ∧ p1)) ∨ ((p6 ∧ p1) → (p4 ∨ p3))) := by
          apply Or.inr
          intro assump_13
          cases assump_13
          case intro assump_14 assump_15 =>
            have assump_99 : (((p7 ∨ p1) ∨ (p2 ∧ p1)) ∨ ((p6 ∧ p1) → (p4 ∨ p3))) := by
              apply Or.inl
              apply Or.inl
              apply Or.inr
              exact assump_15
            let assump_22 := assump_3 assump_99
            apply False.elim assump_22
        let assump_12 := assump_3 assump_98
        apply False.elim assump_12
      case inr assump_7 =>
        cases assump_7
        case intro assump_29 assump_30 =>
          have assump_100 : (((p7 ∨ p1) ∨ (p2 ∧ p1)) ∨ ((p6 ∧ p1) → (p4 ∨ p3))) := by
            apply Or.inr
            intro assump_38
            cases assump_38
            case intro assump_39 assump_40 =>
              have assump_101 : (((p7 ∨ p1) ∨ (p2 ∧ p1)) ∨ ((p6 ∧ p1) → (p4 ∨ p3))) := by
                apply Or.inl
                apply Or.inl
                apply Or.inr
                exact assump_40
              let assump_47 := assump_3 assump_101
              apply False.elim assump_47
          let assump_37 := assump_3 assump_100
          apply False.elim assump_37
    case inr assump_5 =>
      cases assump_5
      case inl assump_54 =>
        have assump_102 : (((p7 ∨ p1) ∨ (p2 ∧ p1)) ∨ ((p6 ∧ p1) → (p4 ∨ p3))) := by
          apply Or.inr
          intro assump_61
          cases assump_61
          case intro assump_62 assump_63 =>
            have assump_103 : (((p7 ∨ p1) ∨ (p2 ∧ p1)) ∨ ((p6 ∧ p1) → (p4 ∨ p3))) := by
              apply Or.inl
              apply Or.inl
              apply Or.inr
              exact assump_63
            let assump_70 := assump_3 assump_103
            apply False.elim assump_70
        let assump_60 := assump_3 assump_102
        apply False.elim assump_60
      case inr assump_55 =>
        have assump_104 : (((p7 ∨ p1) ∨ (p2 ∧ p1)) ∨ ((p6 ∧ p1) → (p4 ∨ p3))) := by
          apply Or.inr
          intro assump_82
          cases assump_82
          case intro assump_83 assump_84 =>
            have assump_105 : (((p7 ∨ p1) ∨ (p2 ∧ p1)) ∨ ((p6 ∧ p1) → (p4 ∨ p3))) := by
              apply Or.inl
              apply Or.inl
              apply Or.inr
              exact assump_84
            let assump_91 := assump_3 assump_105
            apply False.elim assump_91
        let assump_81 := assump_3 assump_104
        apply False.elim assump_81


variable (p0 p1 p4 p3 p2 p6 : Prop)
theorem file28_39669 : ((((((p4 ∨ p0) → (p3 → False)) ∨ ((p0 ∨ True) ∨ (True ∨ p1))) → False) ∧ ((((False ∧ p0) → False) → False) ∧ (((False → False) → (True ∧ False)) ∧ ((p6 ∨ p6) ∨ (p2 → p3))))) → False) := by
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
            have assump_54 : (False → False) := by
              intro assump_22
              apply False.elim assump_22
            let assump_21 := assump_10 assump_54
            let assump_25 := And.right assump_21
            apply False.elim assump_25
          case inr assump_17 =>
            have assump_55 : (False → False) := by
              intro assump_34
              apply False.elim assump_34
            let assump_33 := assump_10 assump_55
            let assump_37 := And.right assump_33
            apply False.elim assump_37
        case inr assump_15 =>
          have assump_56 : (False → False) := by
            intro assump_46
            apply False.elim assump_46
          let assump_45 := assump_10 assump_56
          let assump_49 := And.right assump_45
          apply False.elim assump_49


variable (p7 p6 p4 p2 p1 p0 p3 p5 : Prop)
theorem file28_41047 : (((((p2 ∨ p6) → (False ∧ p4)) ∧ ((True → False) → (p4 → p6))) ∧ (((False → False) ∨ (p7 → p1)) → False)) → ((((p1 ∧ p5) ∧ (p6 → False)) ∨ ((p3 ∧ False) ∧ (p7 → p5))) ∨ (((True → p4) ∧ (p0 ∧ p4)) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply Or.inr
      intro assump_12
      cases assump_12
      case intro assump_13 assump_14 =>
        cases assump_14
        case intro assump_17 assump_18 =>
          have assump_34 : ((False → False) ∨ (p7 → p1)) := by
            apply Or.inl
            intro assump_28
            apply False.elim assump_28
          let assump_27 := assump_3 assump_34
          apply False.elim assump_27


variable (p7 p2 p0 p3 p6 p5 p4 : Prop)
theorem file28_41852 : (((((p4 ∧ p0) ∨ (p6 → p4)) ∨ ((p5 → p2) ∧ (p0 → False))) ∧ (((p4 ∧ False) → (p7 ∧ p5)) → False)) → ((((p5 ∨ p6) ∧ (False ∨ p6)) → False) → (((p3 → p5) → (p4 ∨ p5)) ∧ ((p6 → False) → False)))) := by
  intro assump_31
  intro assump_32
  apply And.intro
  intro assump_33
  cases assump_31
  case intro assump_38 assump_39 =>
    cases assump_38
    case inl assump_40 =>
      cases assump_40
      case inl assump_42 =>
        cases assump_42
        case intro assump_44 assump_45 =>
          apply Or.inl
          exact assump_44
      case inr assump_43 =>
        have assump_180 : ((p4 ∧ False) → (p7 ∧ p5)) := by
          intro assump_57
          apply And.intro
          cases assump_57
          case intro assump_58 assump_59 =>
            apply False.elim assump_59
          cases assump_57
          case intro assump_64 assump_65 =>
            apply False.elim assump_65
        let assump_56 := assump_39 assump_180
        apply False.elim assump_56
    case inr assump_41 =>
      cases assump_41
      case intro assump_73 assump_74 =>
        have assump_181 : ((p4 ∧ False) → (p7 ∧ p5)) := by
          intro assump_82
          apply And.intro
          cases assump_82
          case intro assump_83 assump_84 =>
            apply False.elim assump_84
          cases assump_82
          case intro assump_89 assump_90 =>
            apply False.elim assump_90
        let assump_81 := assump_39 assump_181
        apply False.elim assump_81
  intro assump_98
  cases assump_31
  case intro assump_103 assump_104 =>
    cases assump_103
    case inl assump_105 =>
      cases assump_105
      case inl assump_107 =>
        cases assump_107
        case intro assump_109 assump_110 =>
          have assump_182 : ((p4 ∧ False) → (p7 ∧ p5)) := by
            intro assump_118
            apply And.intro
            cases assump_118
            case intro assump_119 assump_120 =>
              apply False.elim assump_120
            cases assump_118
            case intro assump_125 assump_126 =>
              apply False.elim assump_126
          let assump_117 := assump_104 assump_182
          apply False.elim assump_117
      case inr assump_108 =>
        have assump_183 : ((p4 ∧ False) → (p7 ∧ p5)) := by
          intro assump_139
          apply And.intro
          cases assump_139
          case intro assump_140 assump_141 =>
            apply False.elim assump_141
          cases assump_139
          case intro assump_146 assump_147 =>
            apply False.elim assump_147
        let assump_138 := assump_104 assump_183
        apply False.elim assump_138
    case inr assump_106 =>
      cases assump_106
      case intro assump_155 assump_156 =>
        have assump_184 : ((p4 ∧ False) → (p7 ∧ p5)) := by
          intro assump_164
          apply And.intro
          cases assump_164
          case intro assump_165 assump_166 =>
            apply False.elim assump_166
          cases assump_164
          case intro assump_171 assump_172 =>
            apply False.elim assump_172
        let assump_163 := assump_104 assump_184
        apply False.elim assump_163


variable (p5 p2 p1 p0 p6 p7 p4 : Prop)
theorem file28_45038 : ((((((p2 ∧ p5) ∨ (p1 → p7)) → False) → (((p6 ∧ p6) ∨ (p4 → False)) → ((p7 ∧ p1) ∧ (p2 ∨ p7)))) ∧ ((((p2 ∨ p7) ∧ (False ∨ True)) ∧ ((True → False) ∧ (False ∧ p1))) ∧ (((p6 ∧ p6) → False) ∨ ((p0 → p1) → (p7 ∧ p0))))) → False) := by
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
            case inl assump_16 =>
              apply False.elim assump_16
            case inr assump_17 =>
              cases assump_9
              case intro assump_22 assump_23 =>
                cases assump_23
                case intro assump_26 assump_27 =>
                  apply False.elim assump_26
          case inr assump_13 =>
            cases assump_11
            case inl assump_32 =>
              apply False.elim assump_32
            case inr assump_33 =>
              cases assump_9
              case intro assump_38 assump_39 =>
                cases assump_39
                case intro assump_42 assump_43 =>
                  apply False.elim assump_42


variable (p5 p1 p2 p6 p0 : Prop)
theorem file28_46344 : (((((p1 ∧ p6) ∧ (p0 ∨ p2)) → ((p5 ∨ p6) ∨ (True ∨ p2))) → False) → False) := by
  intro assump_1
  have assump_23 : (((p1 ∧ p6) ∧ (p0 ∨ p2)) → ((p5 ∨ p6) ∨ (True ∨ p2))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case inl assump_14 =>
          apply Or.inl
          apply Or.inr
          exact assump_9
        case inr assump_15 =>
          apply Or.inl
          apply Or.inr
          exact assump_9
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p6 p0 p4 p7 p1 : Prop)
theorem file28_47000 : (((((p4 ∨ p6) ∨ (False ∨ True)) ∨ ((p4 ∧ p6) → False)) ∧ (((p0 ∧ False) → (p7 ∨ p6)) → False)) → ((((False → False) ∧ (p6 → False)) ∨ ((p0 → p0) → (p1 ∨ p0))) ∨ (((p1 ∨ p4) ∨ (p6 ∧ p7)) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          apply Or.inl
          apply Or.inl
          apply And.intro
          intro assump_14
          apply False.elim assump_14
          intro assump_17
          have assump_102 : ((p0 ∧ False) → (p7 ∨ p6)) := by
            intro assump_22
            cases assump_22
            case intro assump_23 assump_24 =>
              apply False.elim assump_24
          let assump_21 := assump_3 assump_102
          apply False.elim assump_21
        case inr assump_9 =>
          apply Or.inl
          apply Or.inl
          apply And.intro
          intro assump_36
          apply False.elim assump_36
          intro assump_39
          have assump_103 : ((p0 ∧ False) → (p7 ∨ p6)) := by
            intro assump_44
            cases assump_44
            case intro assump_45 assump_46 =>
              apply False.elim assump_46
          let assump_43 := assump_3 assump_103
          apply False.elim assump_43
      case inr assump_7 =>
        cases assump_7
        case inl assump_54 =>
          apply False.elim assump_54
        case inr assump_55 =>
          apply Or.inl
          apply Or.inl
          apply And.intro
          intro assump_62
          apply False.elim assump_62
          intro assump_65
          have assump_104 : ((p0 ∧ False) → (p7 ∨ p6)) := by
            intro assump_70
            cases assump_70
            case intro assump_71 assump_72 =>
              apply False.elim assump_72
          let assump_69 := assump_3 assump_104
          apply False.elim assump_69
    case inr assump_5 =>
      apply Or.inl
      apply Or.inl
      apply And.intro
      intro assump_84
      apply False.elim assump_84
      intro assump_87
      have assump_105 : ((p0 ∧ False) → (p7 ∨ p6)) := by
        intro assump_92
        cases assump_92
        case intro assump_93 assump_94 =>
          apply False.elim assump_94
      let assump_91 := assump_3 assump_105
      apply False.elim assump_91


variable (p5 p2 p4 : Prop)
theorem file28_49411 : ((((((p5 ∨ p5) → (p4 ∧ p5)) ∧ ((p2 ∧ p4) ∧ (p2 → False))) → False) → False) → False) := by
  intro assump_1
  have assump_27 : ((((p5 ∨ p5) → (p4 ∧ p5)) ∧ ((p2 ∧ p4) ∧ (p2 → False))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          have assump_28 : p2 := by
            exact assump_12
          let assump_20 := assump_11 assump_28
          apply False.elim assump_20
  let assump_4 := assump_1 assump_27
  apply False.elim assump_4


variable (p4 p2 p5 p6 p7 p3 p1 p0 : Prop)
theorem file28_50089 : ((((((False ∨ p3) → (p0 ∨ p6)) → ((p6 ∧ p6) → (p2 ∨ p0))) ∧ (((p4 → False) ∧ (True → False)) → False)) ∧ ((((p7 ∨ p4) ∨ (p1 → False)) ∨ ((p2 ∧ p1) ∧ (p7 → False))) ∧ (((True ∨ p6) → (True ∨ p6)) → ((p0 → p5) ∧ (False ∧ p6))))) → False) := by
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
            cases assump_14
            case inl assump_16 =>
              have assump_98 : ((True ∨ p6) → (True ∨ p6)) := by
                intro assump_23
                cases assump_23
                case inl assump_24 =>
                  apply Or.inl
                  apply True.intro
                case inr assump_25 =>
                  apply Or.inl
                  apply True.intro
              let assump_22 := assump_11 assump_98
              let assump_30 := And.right assump_22
              let assump_32 := And.left assump_30
              apply False.elim assump_32
            case inr assump_17 =>
              have assump_99 : ((True ∨ p6) → (True ∨ p6)) := by
                intro assump_41
                cases assump_41
                case inl assump_42 =>
                  apply Or.inl
                  apply True.intro
                case inr assump_43 =>
                  apply Or.inl
                  apply True.intro
              let assump_40 := assump_11 assump_99
              let assump_48 := And.right assump_40
              let assump_50 := And.left assump_48
              apply False.elim assump_50
          case inr assump_15 =>
            have assump_100 : ((True ∨ p6) → (True ∨ p6)) := by
              intro assump_59
              cases assump_59
              case inl assump_60 =>
                apply Or.inl
                apply True.intro
              case inr assump_61 =>
                apply Or.inl
                apply True.intro
            let assump_58 := assump_11 assump_100
            let assump_66 := And.right assump_58
            let assump_68 := And.left assump_66
            apply False.elim assump_68
        case inr assump_13 =>
          cases assump_13
          case intro assump_72 assump_73 =>
            cases assump_72
            case intro assump_74 assump_75 =>
              have assump_101 : ((True ∨ p6) → (True ∨ p6)) := by
                intro assump_85
                cases assump_85
                case inl assump_86 =>
                  apply Or.inl
                  apply True.intro
                case inr assump_87 =>
                  apply Or.inl
                  apply True.intro
              let assump_84 := assump_11 assump_101
              let assump_92 := And.right assump_84
              let assump_94 := And.left assump_92
              apply False.elim assump_94


variable (p5 p0 p2 p7 p4 p6 : Prop)
theorem file28_53087 : (((((p0 → p2) → False) → ((p5 → False) → (p0 → True))) ∨ (((False → False) → (p6 ∨ p4)) → False)) ∧ ((((p0 ∧ p7) → (p4 → False)) → ((p5 → p0) → (True ∨ True))) ∨ (((p4 ∧ p2) → False) ∧ ((p6 ∨ p7) ∧ (p0 → False))))) := by
  apply And.intro
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  apply True.intro
  apply Or.inl
  intro assump_4
  intro assump_5
  apply Or.inl
  apply True.intro


variable (p2 p7 p4 p5 p3 p0 p6 : Prop)
theorem file28_53557 : (((((p5 → p6) → (True ∨ p4)) ∨ ((p3 → False) → (False ∨ False))) ∨ (((p6 ∧ p4) → False) ∨ ((True → False) → False))) ∨ ((((p0 → p0) ∧ (p3 ∨ p7)) → ((p2 → p0) → (p6 ∨ p4))) ∨ (((p6 → True) → False) → False))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inl
  apply True.intro


variable (p1 p6 p7 p3 p5 p4 p0 : Prop)
theorem file28_53930 : ((((((p4 ∨ p5) ∨ (p3 → p7)) → ((False → False) ∨ (p7 → True))) → False) ∧ ((((p4 ∧ p4) ∧ (False ∧ p0)) ∧ ((p1 → True) ∧ (p6 ∨ p3))) → (((p6 → p6) ∨ (p5 → False)) → ((p6 ∧ p5) ∧ (False → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_33 : (((p4 ∨ p5) ∨ (p3 → p7)) → ((False → False) ∨ (p7 → True))) := by
      intro assump_10
      cases assump_10
      case inl assump_11 =>
        cases assump_11
        case inl assump_13 =>
          apply Or.inl
          intro assump_17
          apply False.elim assump_17
        case inr assump_14 =>
          apply Or.inl
          intro assump_22
          apply False.elim assump_22
      case inr assump_12 =>
        apply Or.inl
        intro assump_27
        apply False.elim assump_27
    let assump_9 := assump_2 assump_33
    apply False.elim assump_9


variable (p0 p6 p3 p2 p4 p7 : Prop)
theorem file28_54862 : (((((p7 → False) ∧ (False ∧ p2)) → False) ∨ (((p6 → p7) → False) ∧ ((p4 → False) → False))) ∨ ((((p0 → p0) → (p6 ∧ p0)) ∨ ((True → False) → (True ∧ False))) ∧ (((p7 → False) ∨ (False → p3)) ∧ ((p7 ∨ p4) ∧ (p6 → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      apply False.elim assump_6


variable (p5 p6 p2 p4 p0 p7 p1 : Prop)
theorem file28_55338 : (((((p6 ∧ False) ∧ (p0 → False)) → ((p6 → p1) ∨ (p5 → False))) → (((p6 → False) → False) → ((False → False) ∨ (p2 → p0)))) ∨ ((((p7 → p4) → (p0 → False)) ∧ ((False → False) ∧ (p2 → True))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  apply False.elim assump_7


variable (p5 p3 p4 p2 p1 : Prop)
theorem file28_55709 : ((((((True → False) → False) → ((False → False) → False)) → (((p4 ∨ p2) → (True ∨ p1)) ∨ ((p3 → False) ∧ (p5 ∨ p3)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((True → False) → False) → ((False → False) → False)) → (((p4 ∨ p2) → (True ∨ p1)) ∨ ((p3 → False) ∧ (p5 ∨ p3)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    cases assump_8
    case inl assump_9 =>
      apply Or.inl
      apply True.intro
    case inr assump_10 =>
      apply Or.inl
      apply True.intro
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p7 p3 p4 p0 p6 p1 p2 : Prop)
theorem file28_56346 : (((((p0 → p0) → False) → ((p0 → p4) ∧ (True ∨ p1))) ∨ (((p3 ∨ p1) → (p3 → p6)) ∧ ((p0 → p3) ∨ (p0 ∧ p2)))) ∨ ((((False → p4) → False) ∧ ((p0 ∨ p7) ∨ (p1 → True))) → (((False → False) → False) ∧ ((True ∨ p2) → (p1 ∨ True))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  have assump_16 : (p0 → p0) := by
    intro assump_8
    exact assump_8
  let assump_7 := assump_1 assump_16
  apply False.elim assump_7
  apply Or.inl
  apply True.intro


variable (p3 p1 p6 p0 p4 p2 p7 : Prop)
theorem file28_56894 : (((((False → p7) → (p3 ∧ p4)) ∨ ((p1 → False) ∨ (False ∨ True))) → (((p0 ∨ p3) ∨ (p6 ∧ p6)) → False)) → ((((True ∨ False) → False) → ((p2 → p2) ∨ (p3 ∨ p3))) ∧ (((p1 → False) → (p1 → False)) ∨ ((p2 ∨ False) ∨ (False ∧ p3))))) := by
  intro assump_8
  apply And.intro
  intro assump_9
  apply Or.inl
  intro assump_14
  exact assump_14
  apply Or.inl
  intro assump_19
  intro assump_20
  have assump_29 : p1 := by
    exact assump_20
  let assump_25 := assump_19 assump_29
  apply False.elim assump_25


variable (p7 p1 p5 p0 p4 : Prop)
theorem file28_57453 : (((((p0 → True) ∨ (True ∧ p7)) ∨ ((p5 → False) → (p1 → p4))) → False) → False) := by
  intro assump_1
  have assump_9 : (((p0 → True) ∨ (True ∧ p7)) ∨ ((p5 → False) → (p1 → p4))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_9
  apply False.elim assump_4


variable (p2 p7 p1 p6 p4 p0 p5 : Prop)
theorem file28_57839 : (((((p5 → True) → False) ∧ ((True ∧ p5) → False)) → False) ∧ ((((p0 → False) ∧ (p4 → False)) → ((False → False) ∨ (False → p6))) ∨ (((True → False) ∧ (p2 ∨ p7)) ∧ ((p5 → p0) ∨ (p0 ∧ p1))))) := by
  apply And.intro
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_24 : (p5 → True) := by
      intro assump_10
      apply True.intro
    let assump_9 := assump_2 assump_24
    apply False.elim assump_9
  apply Or.inl
  intro assump_14
  cases assump_14
  case intro assump_15 assump_16 =>
    apply Or.inl
    intro assump_21
    apply False.elim assump_21


variable (p0 p5 p7 p1 p4 p2 p3 : Prop)
theorem file28_58492 : (((((False → False) ∨ (p5 → p7)) → ((False ∧ True) → (p2 → p1))) ∨ (((p7 ∨ p7) ∨ (p0 ∧ p7)) ∧ ((p4 ∧ p5) ∧ (p5 → False)))) ∨ ((((False → p0) ∨ (p3 ∨ p1)) → ((p7 → False) → (p7 ∨ p5))) ∨ (((p2 → False) → False) ∨ ((True ∧ True) ∨ (p4 ∨ False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_9
  intro assump_10
  intro assump_11
  cases assump_10
  case intro assump_14 assump_15 =>
    apply False.elim assump_14


variable (p0 p4 p7 p5 p2 p3 p6 : Prop)
theorem file28_58975 : (((((p5 ∧ False) → (p2 → False)) ∧ ((p4 ∨ p2) → (p6 ∧ p3))) ∨ (((p6 → False) ∧ (p2 ∨ p5)) ∧ ((False → p5) → False))) → ((((True ∧ p2) → (p7 → p0)) ∧ ((True ∨ p7) → False)) → (((p0 → False) ∨ (False ∨ p0)) → ((True ∧ True) → False)))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_3
    case inl assump_11 =>
      cases assump_2
      case intro assump_15 assump_16 =>
        cases assump_1
        case inl assump_21 =>
          cases assump_21
          case intro assump_23 assump_24 =>
            have assump_121 : (True ∨ p7) := by
              apply Or.inl
              apply True.intro
            let assump_31 := assump_16 assump_121
            apply False.elim assump_31
        case inr assump_22 =>
          cases assump_22
          case intro assump_35 assump_36 =>
            cases assump_35
            case intro assump_37 assump_38 =>
              cases assump_38
              case inl assump_41 =>
                have assump_122 : (False → p5) := by
                  intro assump_48
                  apply False.elim assump_48
                let assump_47 := assump_36 assump_122
                apply False.elim assump_47
              case inr assump_42 =>
                have assump_123 : (False → p5) := by
                  intro assump_59
                  apply False.elim assump_59
                let assump_58 := assump_36 assump_123
                apply False.elim assump_58
    case inr assump_12 =>
      cases assump_12
      case inl assump_65 =>
        apply False.elim assump_65
      case inr assump_66 =>
        cases assump_2
        case intro assump_71 assump_72 =>
          cases assump_1
          case inl assump_77 =>
            cases assump_77
            case intro assump_79 assump_80 =>
              have assump_124 : (True ∨ p7) := by
                apply Or.inl
                apply True.intro
              let assump_87 := assump_72 assump_124
              apply False.elim assump_87
          case inr assump_78 =>
            cases assump_78
            case intro assump_91 assump_92 =>
              cases assump_91
              case intro assump_93 assump_94 =>
                cases assump_94
                case inl assump_97 =>
                  have assump_125 : (False → p5) := by
                    intro assump_104
                    apply False.elim assump_104
                  let assump_103 := assump_92 assump_125
                  apply False.elim assump_103
                case inr assump_98 =>
                  have assump_126 : (False → p5) := by
                    intro assump_115
                    apply False.elim assump_115
                  let assump_114 := assump_92 assump_126
                  apply False.elim assump_114


variable (p7 p0 p6 p4 p2 p5 p3 : Prop)
theorem file28_61873 : (((((False ∧ p6) → (p0 ∧ p7)) ∧ ((p6 ∧ p6) → (False ∨ True))) → False) → ((((p2 ∧ p3) ∨ (p4 ∨ p5)) ∨ ((p0 → False) ∨ (p0 ∧ p6))) ∨ (((p6 → p0) → False) → False))) := by
  intro assump_1
  apply Or.inl
  apply Or.inr
  apply Or.inl
  intro assump_4
  have assump_28 : (((False ∧ p6) → (p0 ∧ p7)) ∧ ((p6 ∧ p6) → (False ∨ True))) := by
    apply And.intro
    intro assump_9
    apply And.intro
    cases assump_9
    case intro assump_10 assump_11 =>
      apply False.elim assump_10
    cases assump_9
    case intro assump_14 assump_15 =>
      apply False.elim assump_14
    intro assump_18
    cases assump_18
    case intro assump_19 assump_20 =>
      apply Or.inr
      apply True.intro
  let assump_8 := assump_1 assump_28
  apply False.elim assump_8


variable (p6 p2 p3 p7 p1 p5 p0 : Prop)
theorem file28_62693 : (((((p5 ∨ p6) → (p7 → False)) ∧ ((p0 ∨ False) ∨ (True ∧ p0))) → False) → ((((p3 ∨ p2) ∨ (p2 ∧ p1)) ∧ ((p3 ∨ False) → False)) ∨ (((True → False) ∧ (True → False)) → False))) := by
  intro assump_1
  apply Or.inr
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    have assump_15 : True := by
      apply True.intro
    let assump_11 := assump_6 assump_15
    apply False.elim assump_11


variable (p0 p6 p1 p3 p4 p5 p7 p2 : Prop)
theorem file28_63164 : (((((False ∧ p4) ∧ (p7 → p1)) ∨ ((p0 ∧ False) ∧ (p3 → p2))) → (((p7 → True) → False) → False)) ∨ ((((True ∨ p5) ∨ (p6 → p5)) ∨ ((p4 → False) ∨ (p5 ∨ p5))) ∧ (((p0 ∨ True) ∧ (False ∧ p4)) ∨ ((p0 ∧ p1) ∨ (p0 → False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        apply False.elim assump_9
  case inr assump_6 =>
    cases assump_6
    case intro assump_13 assump_14 =>
      cases assump_13
      case intro assump_15 assump_16 =>
        apply False.elim assump_16


variable (p5 p1 p3 p7 p0 p4 p2 : Prop)
theorem file28_63867 : (((((p3 → p0) ∨ (p4 → False)) → False) → (((p5 ∨ p4) ∨ (False → p3)) ∨ ((p4 ∨ p0) ∨ (p2 ∧ p0)))) ∧ ((((p3 → True) → False) → False) ∨ (((p7 → False) → (p5 ∧ p5)) ∧ ((p7 ∧ p5) → (p5 ∨ p1))))) := by
  apply And.intro
  intro assump_1
  apply Or.inl
  apply Or.inr
  intro assump_4
  apply False.elim assump_4
  apply Or.inl
  intro assump_7
  have assump_15 : (p3 → True) := by
    intro assump_11
    apply True.intro
  let assump_10 := assump_7 assump_15
  apply False.elim assump_10


variable (p6 p4 p2 p0 p3 p1 p5 : Prop)
theorem file28_64414 : ((((((p5 ∧ p1) → (False ∧ p4)) ∧ ((p0 → p2) ∨ (p3 → False))) → False) ∧ ((((p5 → False) ∧ (p0 → False)) ∧ ((p6 ∨ p0) ∧ (p6 ∧ False))) ∧ (((p6 → p6) → False) → False))) → False) := by
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
            case inl assump_18 =>
              cases assump_17
              case intro assump_22 assump_23 =>
                apply False.elim assump_23
            case inr assump_19 =>
              cases assump_17
              case intro assump_30 assump_31 =>
                apply False.elim assump_31


variable (p5 p7 p3 p4 p1 p0 p2 p6 : Prop)
theorem file28_65317 : (((((p6 ∧ p0) → False) ∧ ((p5 ∨ True) → False)) ∧ (((p5 ∨ p1) ∧ (True ∨ False)) ∨ ((p2 ∨ p0) → (p2 ∨ p2)))) → ((((p4 → p7) → (p0 ∧ p1)) ∨ ((p1 → False) ∨ (p2 → p3))) ∧ (((p4 ∨ False) ∨ (p5 → p7)) → ((p4 ∧ p5) ∧ (True → p2))))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case inl assump_10 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_12
          case inl assump_14 =>
            cases assump_13
            case inl assump_18 =>
              apply Or.inl
              intro assump_22
              apply And.intro
              have assump_370 : (p5 ∨ True) := by
                apply Or.inl
                exact assump_14
              let assump_27 := assump_5 assump_370
              apply False.elim assump_27
              have assump_371 : (p5 ∨ True) := by
                apply Or.inl
                exact assump_14
              let assump_35 := assump_5 assump_371
              apply False.elim assump_35
            case inr assump_19 =>
              apply False.elim assump_19
          case inr assump_15 =>
            cases assump_13
            case inl assump_43 =>
              apply Or.inl
              intro assump_47
              apply And.intro
              have assump_372 : (p5 ∨ True) := by
                apply Or.inr
                apply True.intro
              let assump_52 := assump_5 assump_372
              apply False.elim assump_52
              exact assump_15
            case inr assump_44 =>
              apply False.elim assump_44
      case inr assump_11 =>
        apply Or.inl
        intro assump_62
        apply And.intro
        have assump_373 : (p5 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_67 := assump_5 assump_373
        apply False.elim assump_67
        have assump_374 : (p5 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_75 := assump_5 assump_374
        apply False.elim assump_75
  intro assump_79
  apply And.intro
  apply And.intro
  cases assump_79
  case inl assump_80 =>
    cases assump_80
    case inl assump_82 =>
      cases assump_1
      case intro assump_86 assump_87 =>
        cases assump_86
        case intro assump_88 assump_89 =>
          cases assump_87
          case inl assump_94 =>
            cases assump_94
            case intro assump_96 assump_97 =>
              cases assump_96
              case inl assump_98 =>
                cases assump_97
                case inl assump_102 =>
                  exact assump_82
                case inr assump_103 =>
                  apply False.elim assump_103
              case inr assump_99 =>
                cases assump_97
                case inl assump_110 =>
                  exact assump_82
                case inr assump_111 =>
                  apply False.elim assump_111
          case inr assump_95 =>
            exact assump_82
    case inr assump_83 =>
      apply False.elim assump_83
  case inr assump_81 =>
    cases assump_1
    case intro assump_122 assump_123 =>
      cases assump_122
      case intro assump_124 assump_125 =>
        cases assump_123
        case inl assump_130 =>
          cases assump_130
          case intro assump_132 assump_133 =>
            cases assump_132
            case inl assump_134 =>
              cases assump_133
              case inl assump_138 =>
                have assump_375 : (p5 ∨ True) := by
                  apply Or.inl
                  exact assump_134
                let assump_143 := assump_125 assump_375
                apply False.elim assump_143
              case inr assump_139 =>
                apply False.elim assump_139
            case inr assump_135 =>
              cases assump_133
              case inl assump_151 =>
                have assump_376 : (p5 ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_156 := assump_125 assump_376
                apply False.elim assump_156
              case inr assump_152 =>
                apply False.elim assump_152
        case inr assump_131 =>
          have assump_377 : (p5 ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_165 := assump_125 assump_377
          apply False.elim assump_165
  cases assump_79
  case inl assump_169 =>
    cases assump_169
    case inl assump_171 =>
      cases assump_1
      case intro assump_175 assump_176 =>
        cases assump_175
        case intro assump_177 assump_178 =>
          cases assump_176
          case inl assump_183 =>
            cases assump_183
            case intro assump_185 assump_186 =>
              cases assump_185
              case inl assump_187 =>
                cases assump_186
                case inl assump_191 =>
                  exact assump_187
                case inr assump_192 =>
                  apply False.elim assump_192
              case inr assump_188 =>
                cases assump_186
                case inl assump_199 =>
                  have assump_378 : (p5 ∨ True) := by
                    apply Or.inr
                    apply True.intro
                  let assump_204 := assump_178 assump_378
                  apply False.elim assump_204
                case inr assump_200 =>
                  apply False.elim assump_200
          case inr assump_184 =>
            have assump_379 : (p5 ∨ True) := by
              apply Or.inr
              apply True.intro
            let assump_213 := assump_178 assump_379
            apply False.elim assump_213
    case inr assump_172 =>
      apply False.elim assump_172
  case inr assump_170 =>
    cases assump_1
    case intro assump_221 assump_222 =>
      cases assump_221
      case intro assump_223 assump_224 =>
        cases assump_222
        case inl assump_229 =>
          cases assump_229
          case intro assump_231 assump_232 =>
            cases assump_231
            case inl assump_233 =>
              cases assump_232
              case inl assump_237 =>
                exact assump_233
              case inr assump_238 =>
                apply False.elim assump_238
            case inr assump_234 =>
              cases assump_232
              case inl assump_245 =>
                have assump_380 : (p5 ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_250 := assump_224 assump_380
                apply False.elim assump_250
              case inr assump_246 =>
                apply False.elim assump_246
        case inr assump_230 =>
          have assump_381 : (p5 ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_259 := assump_224 assump_381
          apply False.elim assump_259
  intro assump_263
  cases assump_79
  case inl assump_266 =>
    cases assump_266
    case inl assump_268 =>
      cases assump_1
      case intro assump_272 assump_273 =>
        cases assump_272
        case intro assump_274 assump_275 =>
          cases assump_273
          case inl assump_280 =>
            cases assump_280
            case intro assump_282 assump_283 =>
              cases assump_282
              case inl assump_284 =>
                cases assump_283
                case inl assump_288 =>
                  have assump_382 : (p5 ∨ True) := by
                    apply Or.inl
                    exact assump_284
                  let assump_293 := assump_275 assump_382
                  apply False.elim assump_293
                case inr assump_289 =>
                  apply False.elim assump_289
              case inr assump_285 =>
                cases assump_283
                case inl assump_301 =>
                  have assump_383 : (p5 ∨ True) := by
                    apply Or.inr
                    apply True.intro
                  let assump_306 := assump_275 assump_383
                  apply False.elim assump_306
                case inr assump_302 =>
                  apply False.elim assump_302
          case inr assump_281 =>
            have assump_384 : (p5 ∨ True) := by
              apply Or.inr
              apply True.intro
            let assump_315 := assump_275 assump_384
            apply False.elim assump_315
    case inr assump_269 =>
      apply False.elim assump_269
  case inr assump_267 =>
    cases assump_1
    case intro assump_323 assump_324 =>
      cases assump_323
      case intro assump_325 assump_326 =>
        cases assump_324
        case inl assump_331 =>
          cases assump_331
          case intro assump_333 assump_334 =>
            cases assump_333
            case inl assump_335 =>
              cases assump_334
              case inl assump_339 =>
                have assump_385 : (p5 ∨ True) := by
                  apply Or.inl
                  exact assump_335
                let assump_344 := assump_326 assump_385
                apply False.elim assump_344
              case inr assump_340 =>
                apply False.elim assump_340
            case inr assump_336 =>
              cases assump_334
              case inl assump_352 =>
                have assump_386 : (p5 ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_357 := assump_326 assump_386
                apply False.elim assump_357
              case inr assump_353 =>
                apply False.elim assump_353
        case inr assump_332 =>
          have assump_387 : (p5 ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_366 := assump_326 assump_387
          apply False.elim assump_366


variable (p5 p2 p6 p3 p1 p4 p7 p0 : Prop)
theorem file28_75181 : (((((p6 → p5) ∧ (True → False)) ∧ ((False → p0) → (p4 → False))) → False) ∨ ((((p7 ∧ p2) ∨ (p2 ∧ True)) → ((p1 ∨ p6) ∨ (p3 → p3))) ∨ (((p1 → False) → False) ∨ ((p6 ∧ p4) ∧ (True ∨ p6))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_21 : True := by
        apply True.intro
      let assump_17 := assump_5 assump_21
      apply False.elim assump_17


variable (p4 p7 p0 p5 p2 p1 p3 : Prop)
theorem file28_75710 : (((((p7 ∨ p1) → False) → ((True → p4) ∧ (False → p4))) → False) → ((((True ∨ p2) ∧ (p1 ∧ False)) ∨ ((p0 ∧ p2) → (p3 → p3))) ∨ (((p5 → p2) ∧ (p2 → False)) ∨ ((False → False) → False)))) := by
  intro assump_1
  apply Or.inl
  apply Or.inr
  intro assump_4
  intro assump_5
  cases assump_4
  case intro assump_8 assump_9 =>
    exact assump_5


variable (p6 p5 p4 p7 p2 : Prop)
theorem file28_76109 : (((((p2 ∨ p7) → False) ∨ ((p6 → False) → (p7 ∨ p6))) ∧ (((False ∧ p4) → (p5 ∨ p4)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_32 : ((False ∧ p4) → (p5 ∨ p4)) := by
        intro assump_11
        cases assump_11
        case intro assump_12 assump_13 =>
          apply False.elim assump_12
      let assump_10 := assump_3 assump_32
      apply False.elim assump_10
    case inr assump_5 =>
      have assump_33 : ((False ∧ p4) → (p5 ∨ p4)) := by
        intro assump_24
        cases assump_24
        case intro assump_25 assump_26 =>
          apply False.elim assump_25
      let assump_23 := assump_3 assump_33
      apply False.elim assump_23


variable (p2 p5 p6 p3 p7 p0 p4 p1 : Prop)
theorem file28_76936 : (((((p4 → p5) ∧ (p5 ∨ p7)) ∧ ((p2 ∨ p1) ∨ (p4 ∧ False))) ∧ (((p7 → p6) ∨ (True ∨ p6)) → False)) → ((((p4 → p0) → False) ∨ ((p5 ∧ p1) → (p6 ∧ p1))) → (((p3 ∧ p5) → (p3 ∨ p0)) ∨ ((False ∨ p4) ∨ (p0 → p5))))) := by
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
          cases assump_12
          case inl assump_15 =>
            cases assump_10
            case inl assump_19 =>
              cases assump_19
              case inl assump_21 =>
                apply Or.inl
                intro assump_27
                cases assump_27
                case intro assump_28 assump_29 =>
                  apply Or.inl
                  exact assump_28
              case inr assump_22 =>
                apply Or.inl
                intro assump_38
                cases assump_38
                case intro assump_39 assump_40 =>
                  apply Or.inl
                  exact assump_39
            case inr assump_20 =>
              cases assump_20
              case intro assump_45 assump_46 =>
                apply False.elim assump_46
          case inr assump_16 =>
            cases assump_10
            case inl assump_53 =>
              cases assump_53
              case inl assump_55 =>
                apply Or.inl
                intro assump_61
                cases assump_61
                case intro assump_62 assump_63 =>
                  apply Or.inl
                  exact assump_62
              case inr assump_56 =>
                apply Or.inl
                intro assump_72
                cases assump_72
                case intro assump_73 assump_74 =>
                  apply Or.inl
                  exact assump_73
            case inr assump_54 =>
              cases assump_54
              case intro assump_79 assump_80 =>
                apply False.elim assump_80
  case inr assump_4 =>
    cases assump_1
    case intro assump_87 assump_88 =>
      cases assump_87
      case intro assump_89 assump_90 =>
        cases assump_89
        case intro assump_91 assump_92 =>
          cases assump_92
          case inl assump_95 =>
            cases assump_90
            case inl assump_99 =>
              cases assump_99
              case inl assump_101 =>
                apply Or.inl
                intro assump_107
                cases assump_107
                case intro assump_108 assump_109 =>
                  apply Or.inl
                  exact assump_108
              case inr assump_102 =>
                apply Or.inl
                intro assump_118
                cases assump_118
                case intro assump_119 assump_120 =>
                  apply Or.inl
                  exact assump_119
            case inr assump_100 =>
              cases assump_100
              case intro assump_125 assump_126 =>
                apply False.elim assump_126
          case inr assump_96 =>
            cases assump_90
            case inl assump_133 =>
              cases assump_133
              case inl assump_135 =>
                apply Or.inl
                intro assump_141
                cases assump_141
                case intro assump_142 assump_143 =>
                  apply Or.inl
                  exact assump_142
              case inr assump_136 =>
                apply Or.inl
                intro assump_152
                cases assump_152
                case intro assump_153 assump_154 =>
                  apply Or.inl
                  exact assump_153
            case inr assump_134 =>
              cases assump_134
              case intro assump_159 assump_160 =>
                apply False.elim assump_160


variable (p3 p6 p4 p7 p0 : Prop)
theorem file28_80823 : (((((False ∧ p3) → False) ∧ ((False → False) → False)) → False) ∨ ((((p3 → False) → (p6 ∧ p4)) ∧ ((False ∧ True) ∨ (p7 ∧ p0))) ∨ (((True ∧ False) ∧ (p3 ∧ p6)) ∨ ((p3 ∧ p3) → False)))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : (False → False) := by
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p6 p0 p1 p7 p2 p3 : Prop)
theorem file28_81321 : (((((False ∧ p6) ∧ (p6 → p3)) ∧ ((False → p1) ∨ (p0 → False))) → (((p0 → p7) → (p6 ∧ p7)) → ((p1 → False) ∨ (p6 ∧ p0)))) → ((((True → False) ∧ (False → False)) → ((True ∨ p3) ∨ (False ∧ p7))) ∨ (((p6 → False) ∨ (p6 ∨ p2)) → False))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply Or.inl
    apply Or.inl
    apply True.intro


variable (p7 p5 p3 p2 : Prop)
theorem file28_81769 : ((((((p5 → False) ∨ (False ∧ p7)) → False) → (((p2 ∧ False) ∨ (False ∧ p2)) → ((p3 → False) ∧ (p5 → False)))) → False) → False) := by
  intro assump_1
  have assump_40 : ((((p5 → False) ∨ (False ∧ p7)) → False) → (((p2 ∧ False) ∨ (False ∧ p2)) → ((p3 → False) ∧ (p5 → False)))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    intro assump_7
    cases assump_6
    case inl assump_10 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        apply False.elim assump_13
    case inr assump_11 =>
      cases assump_11
      case intro assump_18 assump_19 =>
        apply False.elim assump_18
    intro assump_22
    cases assump_6
    case inl assump_25 =>
      cases assump_25
      case intro assump_27 assump_28 =>
        apply False.elim assump_28
    case inr assump_26 =>
      cases assump_26
      case intro assump_33 assump_34 =>
        apply False.elim assump_33
  let assump_4 := assump_1 assump_40
  apply False.elim assump_4


variable (p4 p7 p2 p0 p6 p3 p5 p1 : Prop)
theorem file28_82811 : ((((((p4 → p1) ∧ (False → False)) ∧ ((p1 → p1) → (p5 → p4))) → (((p4 → p5) ∨ (p6 → p3)) → ((p6 ∧ p6) ∨ (p1 → False)))) ∧ ((((p5 → p0) ∧ (p7 ∧ p5)) → ((p7 ∨ p2) → (False → p0))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_17 : (((p5 → p0) ∧ (p7 ∧ p5)) → ((p7 ∨ p2) → (False → p0))) := by
      intro assump_9
      intro assump_10
      intro assump_11
      apply False.elim assump_11
    let assump_8 := assump_3 assump_17
    apply False.elim assump_8


variable (p0 p3 p7 : Prop)
theorem file28_83381 : ((((((p7 → False) → (p0 → False)) ∧ ((p3 → p3) → False)) → False) → False) → False) := by
  intro assump_7
  have assump_28 : ((((p7 → False) → (p0 → False)) ∧ ((p3 → p3) → False)) → False) := by
    intro assump_11
    cases assump_11
    case intro assump_12 assump_13 =>
      have assump_29 : (p3 → p3) := by
        intro assump_19
        exact assump_19
      let assump_18 := assump_13 assump_29
      apply False.elim assump_18
  let assump_10 := assump_7 assump_28
  apply False.elim assump_10


variable (p0 p1 p2 p4 p5 p3 : Prop)
theorem file28_83945 : (((((True ∨ p3) → False) ∨ ((p0 ∧ p1) ∧ (p5 → p0))) ∧ (((p3 ∨ p3) ∨ (p4 ∧ p5)) ∨ ((True → False) → False))) → ((((True → False) → False) → False) → (((p2 ∧ False) → False) ∨ ((p4 ∨ p4) → (False ∨ p3))))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      cases assump_6
      case inl assump_11 =>
        cases assump_11
        case inl assump_13 =>
          cases assump_13
          case inl assump_15 =>
            apply Or.inl
            intro assump_19
            cases assump_19
            case intro assump_20 assump_21 =>
              apply False.elim assump_21
          case inr assump_16 =>
            apply Or.inl
            intro assump_28
            cases assump_28
            case intro assump_29 assump_30 =>
              apply False.elim assump_30
        case inr assump_14 =>
          cases assump_14
          case intro assump_35 assump_36 =>
            apply Or.inl
            intro assump_41
            cases assump_41
            case intro assump_42 assump_43 =>
              apply False.elim assump_43
      case inr assump_12 =>
        apply Or.inl
        intro assump_50
        cases assump_50
        case intro assump_51 assump_52 =>
          apply False.elim assump_52
    case inr assump_8 =>
      cases assump_8
      case intro assump_57 assump_58 =>
        cases assump_57
        case intro assump_59 assump_60 =>
          cases assump_6
          case inl assump_67 =>
            cases assump_67
            case inl assump_69 =>
              cases assump_69
              case inl assump_71 =>
                apply Or.inl
                intro assump_75
                cases assump_75
                case intro assump_76 assump_77 =>
                  apply False.elim assump_77
              case inr assump_72 =>
                apply Or.inl
                intro assump_84
                cases assump_84
                case intro assump_85 assump_86 =>
                  apply False.elim assump_86
            case inr assump_70 =>
              cases assump_70
              case intro assump_91 assump_92 =>
                apply Or.inl
                intro assump_97
                cases assump_97
                case intro assump_98 assump_99 =>
                  apply False.elim assump_99
          case inr assump_68 =>
            apply Or.inl
            intro assump_106
            cases assump_106
            case intro assump_107 assump_108 =>
              apply False.elim assump_108


variable (p5 p7 p0 p2 p4 p3 p1 p6 : Prop)
theorem file28_86577 : (((((p4 ∨ p3) → (p4 → p6)) ∧ ((p5 → False) ∧ (p4 → False))) ∧ (((p0 → p1) ∧ (False → False)) ∧ ((p6 → True) ∨ (p1 → False)))) → ((((p7 ∧ p0) ∧ (p1 ∧ p3)) → ((p5 ∨ p2) ∨ (p5 ∨ p0))) ∨ (((p1 ∨ p5) → False) ∨ ((p5 ∨ p0) ∧ (p4 ∨ p2))))) := by
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
            cases assump_15
            case inl assump_22 =>
              apply Or.inl
              intro assump_26
              cases assump_26
              case intro assump_27 assump_28 =>
                cases assump_27
                case intro assump_29 assump_30 =>
                  cases assump_28
                  case intro assump_35 assump_36 =>
                    apply Or.inr
                    apply Or.inr
                    exact assump_30
            case inr assump_23 =>
              apply Or.inl
              intro assump_43
              cases assump_43
              case intro assump_44 assump_45 =>
                cases assump_44
                case intro assump_46 assump_47 =>
                  cases assump_45
                  case intro assump_52 assump_53 =>
                    apply Or.inr
                    apply Or.inr
                    exact assump_47


variable (p6 p3 p1 p2 p4 p7 p0 p5 : Prop)
theorem file28_88105 : (((((False → False) ∨ (False → False)) → ((True → False) → False)) ∨ (((False ∨ False) → (p5 ∧ p1)) ∨ ((False → p6) → (p3 → p7)))) ∧ ((((False ∧ p7) ∧ (p4 ∨ p2)) ∧ ((p2 → False) ∧ (p0 ∨ p6))) → (((p3 ∧ p5) → False) ∨ ((p6 → p5) ∧ (p3 → False))))) := by
  apply And.intro
  apply Or.inl
  intro assump_18
  intro assump_19
  cases assump_18
  case inl assump_22 =>
    have assump_47 : True := by
      apply True.intro
    let assump_27 := assump_19 assump_47
    apply False.elim assump_27
  case inr assump_23 =>
    have assump_48 : True := by
      apply True.intro
    let assump_34 := assump_19 assump_48
    apply False.elim assump_34
  intro assump_38
  cases assump_38
  case intro assump_39 assump_40 =>
    cases assump_39
    case intro assump_41 assump_42 =>
      cases assump_41
      case intro assump_43 assump_44 =>
        apply False.elim assump_43


variable (p6 p2 p5 : Prop)
theorem file28_89025 : (((((True ∨ p6) ∨ (p2 → False)) ∨ ((p5 → False) → (p5 ∧ p5))) → False) → False) := by
  intro assump_1
  have assump_8 : (((True ∨ p6) ∨ (p2 → False)) ∨ ((p5 → False) → (p5 ∧ p5))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p5 p6 p4 p3 : Prop)
theorem file28_89402 : ((((((True → p6) ∧ (False ∧ p3)) ∧ ((False ∧ p4) ∧ (p5 ∨ True))) → False) → False) → False) := by
  intro assump_1
  have assump_19 : ((((True → p6) ∧ (False ∧ p3)) ∧ ((False ∧ p4) ∧ (p5 ∨ True))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          apply False.elim assump_12
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p0 p1 p5 p4 p3 p7 : Prop)
theorem file28_89974 : (((((p0 → False) → (True → True)) ∨ ((p4 ∧ p1) ∧ (p7 ∨ True))) → False) → ((((p3 ∧ False) → (p3 → False)) ∨ ((p5 ∨ True) ∨ (p7 ∧ p3))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    have assump_53 : (((p0 → False) → (True → True)) ∨ ((p4 ∧ p1) ∧ (p7 ∨ True))) := by
      apply Or.inl
      intro assump_10
      intro assump_11
      apply True.intro
    let assump_9 := assump_1 assump_53
    apply False.elim assump_9
  case inr assump_4 =>
    cases assump_4
    case inl assump_15 =>
      cases assump_15
      case inl assump_17 =>
        have assump_54 : (((p0 → False) → (True → True)) ∨ ((p4 ∧ p1) ∧ (p7 ∨ True))) := by
          apply Or.inl
          intro assump_24
          intro assump_25
          apply True.intro
        let assump_23 := assump_1 assump_54
        apply False.elim assump_23
      case inr assump_18 =>
        have assump_55 : (((p0 → False) → (True → True)) ∨ ((p4 ∧ p1) ∧ (p7 ∨ True))) := by
          apply Or.inl
          intro assump_34
          intro assump_35
          apply True.intro
        let assump_33 := assump_1 assump_55
        apply False.elim assump_33
    case inr assump_16 =>
      cases assump_16
      case intro assump_39 assump_40 =>
        have assump_56 : (((p0 → False) → (True → True)) ∨ ((p4 ∧ p1) ∧ (p7 ∨ True))) := by
          apply Or.inl
          intro assump_48
          intro assump_49
          apply True.intro
        let assump_47 := assump_1 assump_56
        apply False.elim assump_47


variable (p2 p6 p1 p0 p7 p3 p4 : Prop)
theorem file28_91558 : (((((p2 ∧ True) ∧ (p4 → False)) ∨ ((False ∨ p0) ∨ (p6 ∧ p3))) ∧ (((p6 ∧ p1) ∧ (p1 → False)) ∧ ((False → p1) ∨ (p2 → p1)))) → ((((p7 → p1) ∨ (p1 → True)) ∨ ((p3 → p0) → False)) ∧ (((p4 ∧ p3) ∨ (True ∧ p0)) ∧ ((p7 ∧ p7) ∧ (p3 → False))))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_3
          case intro assump_16 assump_17 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              cases assump_18
              case intro assump_20 assump_21 =>
                cases assump_17
                case inl assump_28 =>
                  apply Or.inl
                  apply Or.inl
                  intro assump_32
                  exact assump_21
                case inr assump_29 =>
                  apply Or.inl
                  apply Or.inl
                  intro assump_37
                  exact assump_21
    case inr assump_5 =>
      cases assump_5
      case inl assump_40 =>
        cases assump_40
        case inl assump_42 =>
          apply False.elim assump_42
        case inr assump_43 =>
          cases assump_3
          case intro assump_48 assump_49 =>
            cases assump_48
            case intro assump_50 assump_51 =>
              cases assump_50
              case intro assump_52 assump_53 =>
                cases assump_49
                case inl assump_60 =>
                  apply Or.inl
                  apply Or.inl
                  intro assump_64
                  exact assump_53
                case inr assump_61 =>
                  apply Or.inl
                  apply Or.inl
                  intro assump_69
                  exact assump_53
      case inr assump_41 =>
        cases assump_41
        case intro assump_72 assump_73 =>
          cases assump_3
          case intro assump_78 assump_79 =>
            cases assump_78
            case intro assump_80 assump_81 =>
              cases assump_80
              case intro assump_82 assump_83 =>
                cases assump_79
                case inl assump_90 =>
                  apply Or.inl
                  apply Or.inl
                  intro assump_94
                  exact assump_83
                case inr assump_91 =>
                  apply Or.inl
                  apply Or.inl
                  intro assump_99
                  exact assump_83
  apply And.intro
  cases assump_1
  case intro assump_102 assump_103 =>
    cases assump_102
    case inl assump_104 =>
      cases assump_104
      case intro assump_106 assump_107 =>
        cases assump_106
        case intro assump_108 assump_109 =>
          cases assump_103
          case intro assump_116 assump_117 =>
            cases assump_116
            case intro assump_118 assump_119 =>
              cases assump_118
              case intro assump_120 assump_121 =>
                cases assump_117
                case inl assump_128 =>
                  have assump_547 : p1 := by
                    exact assump_121
                  let assump_133 := assump_119 assump_547
                  apply False.elim assump_133
                case inr assump_129 =>
                  have assump_548 : p1 := by
                    exact assump_121
                  let assump_141 := assump_119 assump_548
                  apply False.elim assump_141
    case inr assump_105 =>
      cases assump_105
      case inl assump_145 =>
        cases assump_145
        case inl assump_147 =>
          apply False.elim assump_147
        case inr assump_148 =>
          cases assump_103
          case intro assump_153 assump_154 =>
            cases assump_153
            case intro assump_155 assump_156 =>
              cases assump_155
              case intro assump_157 assump_158 =>
                cases assump_154
                case inl assump_165 =>
                  apply Or.inr
                  apply And.intro
                  apply True.intro
                  exact assump_148
                case inr assump_166 =>
                  apply Or.inr
                  apply And.intro
                  apply True.intro
                  exact assump_148
      case inr assump_146 =>
        cases assump_146
        case intro assump_171 assump_172 =>
          cases assump_103
          case intro assump_177 assump_178 =>
            cases assump_177
            case intro assump_179 assump_180 =>
              cases assump_179
              case intro assump_181 assump_182 =>
                cases assump_178
                case inl assump_189 =>
                  have assump_549 : p1 := by
                    exact assump_182
                  let assump_194 := assump_180 assump_549
                  apply False.elim assump_194
                case inr assump_190 =>
                  have assump_550 : p1 := by
                    exact assump_182
                  let assump_201 := assump_180 assump_550
                  apply False.elim assump_201
  apply And.intro
  apply And.intro
  cases assump_1
  case intro assump_205 assump_206 =>
    cases assump_205
    case inl assump_207 =>
      cases assump_207
      case intro assump_209 assump_210 =>
        cases assump_209
        case intro assump_211 assump_212 =>
          cases assump_206
          case intro assump_219 assump_220 =>
            cases assump_219
            case intro assump_221 assump_222 =>
              cases assump_221
              case intro assump_223 assump_224 =>
                cases assump_220
                case inl assump_231 =>
                  have assump_551 : p1 := by
                    exact assump_224
                  let assump_236 := assump_222 assump_551
                  apply False.elim assump_236
                case inr assump_232 =>
                  have assump_552 : p1 := by
                    exact assump_224
                  let assump_244 := assump_222 assump_552
                  apply False.elim assump_244
    case inr assump_208 =>
      cases assump_208
      case inl assump_248 =>
        cases assump_248
        case inl assump_250 =>
          apply False.elim assump_250
        case inr assump_251 =>
          cases assump_206
          case intro assump_256 assump_257 =>
            cases assump_256
            case intro assump_258 assump_259 =>
              cases assump_258
              case intro assump_260 assump_261 =>
                cases assump_257
                case inl assump_268 =>
                  have assump_553 : p1 := by
                    exact assump_261
                  let assump_273 := assump_259 assump_553
                  apply False.elim assump_273
                case inr assump_269 =>
                  have assump_554 : p1 := by
                    exact assump_261
                  let assump_280 := assump_259 assump_554
                  apply False.elim assump_280
      case inr assump_249 =>
        cases assump_249
        case intro assump_284 assump_285 =>
          cases assump_206
          case intro assump_290 assump_291 =>
            cases assump_290
            case intro assump_292 assump_293 =>
              cases assump_292
              case intro assump_294 assump_295 =>
                cases assump_291
                case inl assump_302 =>
                  have assump_555 : p1 := by
                    exact assump_295
                  let assump_307 := assump_293 assump_555
                  apply False.elim assump_307
                case inr assump_303 =>
                  have assump_556 : p1 := by
                    exact assump_295
                  let assump_314 := assump_293 assump_556
                  apply False.elim assump_314
  cases assump_1
  case intro assump_318 assump_319 =>
    cases assump_318
    case inl assump_320 =>
      cases assump_320
      case intro assump_322 assump_323 =>
        cases assump_322
        case intro assump_324 assump_325 =>
          cases assump_319
          case intro assump_332 assump_333 =>
            cases assump_332
            case intro assump_334 assump_335 =>
              cases assump_334
              case intro assump_336 assump_337 =>
                cases assump_333
                case inl assump_344 =>
                  have assump_557 : p1 := by
                    exact assump_337
                  let assump_349 := assump_335 assump_557
                  apply False.elim assump_349
                case inr assump_345 =>
                  have assump_558 : p1 := by
                    exact assump_337
                  let assump_357 := assump_335 assump_558
                  apply False.elim assump_357
    case inr assump_321 =>
      cases assump_321
      case inl assump_361 =>
        cases assump_361
        case inl assump_363 =>
          apply False.elim assump_363
        case inr assump_364 =>
          cases assump_319
          case intro assump_369 assump_370 =>
            cases assump_369
            case intro assump_371 assump_372 =>
              cases assump_371
              case intro assump_373 assump_374 =>
                cases assump_370
                case inl assump_381 =>
                  have assump_559 : p1 := by
                    exact assump_374
                  let assump_386 := assump_372 assump_559
                  apply False.elim assump_386
                case inr assump_382 =>
                  have assump_560 : p1 := by
                    exact assump_374
                  let assump_393 := assump_372 assump_560
                  apply False.elim assump_393
      case inr assump_362 =>
        cases assump_362
        case intro assump_397 assump_398 =>
          cases assump_319
          case intro assump_403 assump_404 =>
            cases assump_403
            case intro assump_405 assump_406 =>
              cases assump_405
              case intro assump_407 assump_408 =>
                cases assump_404
                case inl assump_415 =>
                  have assump_561 : p1 := by
                    exact assump_408
                  let assump_420 := assump_406 assump_561
                  apply False.elim assump_420
                case inr assump_416 =>
                  have assump_562 : p1 := by
                    exact assump_408
                  let assump_427 := assump_406 assump_562
                  apply False.elim assump_427
  intro assump_431
  cases assump_1
  case intro assump_434 assump_435 =>
    cases assump_434
    case inl assump_436 =>
      cases assump_436
      case intro assump_438 assump_439 =>
        cases assump_438
        case intro assump_440 assump_441 =>
          cases assump_435
          case intro assump_448 assump_449 =>
            cases assump_448
            case intro assump_450 assump_451 =>
              cases assump_450
              case intro assump_452 assump_453 =>
                cases assump_449
                case inl assump_460 =>
                  have assump_563 : p1 := by
                    exact assump_453
                  let assump_465 := assump_451 assump_563
                  apply False.elim assump_465
                case inr assump_461 =>
                  have assump_564 : p1 := by
                    exact assump_453
                  let assump_473 := assump_451 assump_564
                  apply False.elim assump_473
    case inr assump_437 =>
      cases assump_437
      case inl assump_477 =>
        cases assump_477
        case inl assump_479 =>
          apply False.elim assump_479
        case inr assump_480 =>
          cases assump_435
          case intro assump_485 assump_486 =>
            cases assump_485
            case intro assump_487 assump_488 =>
              cases assump_487
              case intro assump_489 assump_490 =>
                cases assump_486
                case inl assump_497 =>
                  have assump_565 : p1 := by
                    exact assump_490
                  let assump_502 := assump_488 assump_565
                  apply False.elim assump_502
                case inr assump_498 =>
                  have assump_566 : p1 := by
                    exact assump_490
                  let assump_509 := assump_488 assump_566
                  apply False.elim assump_509
      case inr assump_478 =>
        cases assump_478
        case intro assump_513 assump_514 =>
          cases assump_435
          case intro assump_519 assump_520 =>
            cases assump_519
            case intro assump_521 assump_522 =>
              cases assump_521
              case intro assump_523 assump_524 =>
                cases assump_520
                case inl assump_531 =>
                  have assump_567 : p1 := by
                    exact assump_524
                  let assump_536 := assump_522 assump_567
                  apply False.elim assump_536
                case inr assump_532 =>
                  have assump_568 : p1 := by
                    exact assump_524
                  let assump_543 := assump_522 assump_568
                  apply False.elim assump_543


variable (p7 p5 p3 p1 p6 p0 : Prop)
theorem file28_104864 : (((((p7 ∧ False) ∧ (p7 ∨ p1)) → ((p5 ∨ p3) ∧ (True → False))) → False) → ((((p0 → False) ∨ (p6 ∨ True)) → False) ∨ (((True ∧ p1) ∧ (p0 ∨ False)) → False))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case inl assump_5 =>
    have assump_89 : (((p7 ∧ False) ∧ (p7 ∨ p1)) → ((p5 ∨ p3) ∧ (True → False))) := by
      intro assump_11
      apply And.intro
      cases assump_11
      case intro assump_12 assump_13 =>
        cases assump_12
        case intro assump_14 assump_15 =>
          apply False.elim assump_15
      intro assump_20
      cases assump_11
      case intro assump_23 assump_24 =>
        cases assump_23
        case intro assump_25 assump_26 =>
          apply False.elim assump_26
    let assump_10 := assump_1 assump_89
    apply False.elim assump_10
  case inr assump_6 =>
    cases assump_6
    case inl assump_34 =>
      have assump_90 : (((p7 ∧ False) ∧ (p7 ∨ p1)) → ((p5 ∨ p3) ∧ (True → False))) := by
        intro assump_40
        apply And.intro
        cases assump_40
        case intro assump_41 assump_42 =>
          cases assump_41
          case intro assump_43 assump_44 =>
            apply False.elim assump_44
        intro assump_49
        cases assump_40
        case intro assump_52 assump_53 =>
          cases assump_52
          case intro assump_54 assump_55 =>
            apply False.elim assump_55
      let assump_39 := assump_1 assump_90
      apply False.elim assump_39
    case inr assump_35 =>
      have assump_91 : (((p7 ∧ False) ∧ (p7 ∨ p1)) → ((p5 ∨ p3) ∧ (True → False))) := by
        intro assump_66
        apply And.intro
        cases assump_66
        case intro assump_67 assump_68 =>
          cases assump_67
          case intro assump_69 assump_70 =>
            apply False.elim assump_70
        intro assump_75
        cases assump_66
        case intro assump_78 assump_79 =>
          cases assump_78
          case intro assump_80 assump_81 =>
            apply False.elim assump_81
      let assump_65 := assump_1 assump_91
      apply False.elim assump_65


variable (p1 p3 p7 p6 p2 : Prop)
theorem file28_106992 : (((((p7 ∨ True) → (False ∧ p1)) ∧ ((False ∧ p2) ∨ (p3 → p7))) → False) ∨ ((((p6 → False) ∧ (p2 → p1)) ∨ ((p3 → False) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_8
    case inr assump_7 =>
      have assump_20 : (p7 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_15 := assump_2 assump_20
      let assump_16 := And.left assump_15
      apply False.elim assump_16


variable (p6 p4 p2 : Prop)
theorem file28_107636 : ((((((p4 ∧ False) → (p6 → p2)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_25 : ((((p4 ∧ False) → (p6 → p2)) → False) → False) := by
    intro assump_5
    have assump_26 : ((p4 ∧ False) → (p6 → p2)) := by
      intro assump_9
      intro assump_10
      cases assump_9
      case intro assump_13 assump_14 =>
        apply False.elim assump_14
    let assump_8 := assump_5 assump_26
    apply False.elim assump_8
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p7 p3 p6 p1 p0 p5 p2 : Prop)
theorem file28_108207 : ((((((p2 ∧ p1) ∧ (p0 → False)) → ((p1 → False) → (False → False))) ∧ (((p5 → False) → False) ∧ ((p2 ∧ p1) ∧ (p7 ∨ p2)))) ∧ ((((p5 → False) → (p3 → False)) ∨ ((p0 ∨ p5) → False)) ∧ (((p6 → False) ∧ (p1 ∧ p0)) ∧ ((p1 → False) ∨ (p0 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_13
            case inl assump_20 =>
              cases assump_3
              case intro assump_24 assump_25 =>
                cases assump_24
                case inl assump_26 =>
                  cases assump_25
                  case intro assump_30 assump_31 =>
                    cases assump_30
                    case intro assump_32 assump_33 =>
                      cases assump_33
                      case intro assump_36 assump_37 =>
                        cases assump_31
                        case inl assump_42 =>
                          have assump_146 : p1 := by
                            exact assump_36
                          let assump_46 := assump_42 assump_146
                          apply False.elim assump_46
                        case inr assump_43 =>
                          have assump_147 : p0 := by
                            exact assump_37
                          let assump_52 := assump_43 assump_147
                          apply False.elim assump_52
                case inr assump_27 =>
                  cases assump_25
                  case intro assump_58 assump_59 =>
                    cases assump_58
                    case intro assump_60 assump_61 =>
                      cases assump_61
                      case intro assump_64 assump_65 =>
                        cases assump_59
                        case inl assump_70 =>
                          have assump_148 : p1 := by
                            exact assump_64
                          let assump_74 := assump_70 assump_148
                          apply False.elim assump_74
                        case inr assump_71 =>
                          have assump_149 : p0 := by
                            exact assump_65
                          let assump_80 := assump_71 assump_149
                          apply False.elim assump_80
            case inr assump_21 =>
              cases assump_3
              case intro assump_86 assump_87 =>
                cases assump_86
                case inl assump_88 =>
                  cases assump_87
                  case intro assump_92 assump_93 =>
                    cases assump_92
                    case intro assump_94 assump_95 =>
                      cases assump_95
                      case intro assump_98 assump_99 =>
                        cases assump_93
                        case inl assump_104 =>
                          have assump_150 : p1 := by
                            exact assump_98
                          let assump_108 := assump_104 assump_150
                          apply False.elim assump_108
                        case inr assump_105 =>
                          have assump_151 : p0 := by
                            exact assump_99
                          let assump_114 := assump_105 assump_151
                          apply False.elim assump_114
                case inr assump_89 =>
                  cases assump_87
                  case intro assump_120 assump_121 =>
                    cases assump_120
                    case intro assump_122 assump_123 =>
                      cases assump_123
                      case intro assump_126 assump_127 =>
                        cases assump_121
                        case inl assump_132 =>
                          have assump_152 : p1 := by
                            exact assump_126
                          let assump_136 := assump_132 assump_152
                          apply False.elim assump_136
                        case inr assump_133 =>
                          have assump_153 : p0 := by
                            exact assump_127
                          let assump_142 := assump_133 assump_153
                          apply False.elim assump_142


variable (p7 p0 p5 p4 p2 p1 p6 : Prop)
theorem file28_112658 : ((((((p4 ∨ p6) → False) → ((p1 → False) ∧ (False → p0))) → False) ∧ ((((p6 → False) ∧ (p6 ∧ p7)) → ((p6 ∧ p5) ∧ (p2 ∨ p2))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_55 : (((p6 → False) ∧ (p6 ∧ p7)) → ((p6 ∧ p5) ∧ (p2 ∨ p2))) := by
      intro assump_9
      apply And.intro
      apply And.intro
      cases assump_9
      case intro assump_10 assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          exact assump_14
      cases assump_9
      case intro assump_20 assump_21 =>
        cases assump_21
        case intro assump_24 assump_25 =>
          have assump_56 : p6 := by
            exact assump_24
          let assump_32 := assump_20 assump_56
          apply False.elim assump_32
      cases assump_9
      case intro assump_36 assump_37 =>
        cases assump_37
        case intro assump_40 assump_41 =>
          have assump_57 : p6 := by
            exact assump_40
          let assump_48 := assump_36 assump_57
          apply False.elim assump_48
    let assump_8 := assump_3 assump_55
    apply False.elim assump_8


variable (p4 p0 p5 p2 p6 p7 : Prop)
theorem file28_113854 : (((((p6 ∧ False) → (False → False)) → False) → False) ∨ ((((p2 → p0) ∧ (True ∨ p2)) ∨ ((p5 → True) ∨ (p4 ∧ False))) → (((p7 ∨ p4) → False) → ((p2 → False) → (p5 ∧ p2))))) := by
  apply Or.inl
  intro assump_1
  have assump_12 : ((p6 ∧ False) → (False → False)) := by
    intro assump_5
    intro assump_6
    apply False.elim assump_6
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p0 p6 : Prop)
theorem file28_114302 : ((((((False ∧ True) → (p0 ∧ p6)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_24 : ((((False ∧ True) → (p0 ∧ p6)) → False) → False) := by
    intro assump_5
    have assump_25 : ((False ∧ True) → (p0 ∧ p6)) := by
      intro assump_9
      apply And.intro
      cases assump_9
      case intro assump_10 assump_11 =>
        apply False.elim assump_10
      cases assump_9
      case intro assump_14 assump_15 =>
        apply False.elim assump_14
    let assump_8 := assump_5 assump_25
    apply False.elim assump_8
  let assump_4 := assump_1 assump_24
  apply False.elim assump_4


variable (p5 p0 p2 p1 : Prop)
theorem file28_114966 : ((((((p1 ∨ p2) ∧ (p0 ∧ p0)) → False) ∨ (((p1 ∧ p5) ∧ (p1 → p5)) → False)) ∧ ((((p0 ∧ False) → False) ∨ ((p2 → True) ∧ (True ∨ p5))) → False)) → False) := by
  intro assump_18
  cases assump_18
  case intro assump_19 assump_20 =>
    cases assump_19
    case inl assump_21 =>
      have assump_53 : (((p0 ∧ False) → False) ∨ ((p2 → True) ∧ (True ∨ p5))) := by
        apply Or.inl
        intro assump_28
        cases assump_28
        case intro assump_29 assump_30 =>
          apply False.elim assump_30
      let assump_27 := assump_20 assump_53
      apply False.elim assump_27
    case inr assump_22 =>
      have assump_54 : (((p0 ∧ False) → False) ∨ ((p2 → True) ∧ (True ∨ p5))) := by
        apply Or.inl
        intro assump_43
        cases assump_43
        case intro assump_44 assump_45 =>
          apply False.elim assump_45
      let assump_42 := assump_20 assump_54
      apply False.elim assump_42


variable (p2 p5 p0 p1 p6 p3 p7 : Prop)
theorem file28_115946 : (((((p7 ∨ False) ∧ (p0 ∧ p0)) ∧ ((p6 → p0) → False)) ∧ (((True ∨ p6) → (p0 ∧ p0)) ∨ ((p1 ∨ True) ∧ (True ∧ True)))) → ((((p7 ∧ p3) ∨ (True ∨ False)) ∨ ((False → False) ∧ (p6 ∧ p1))) ∨ (((p2 → p2) ∧ (p6 ∧ True)) → ((p5 ∧ p1) → False)))) := by
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
            case inl assump_20 =>
              apply Or.inl
              apply Or.inl
              apply Or.inr
              apply Or.inl
              apply True.intro
            case inr assump_21 =>
              cases assump_21
              case intro assump_24 assump_25 =>
                cases assump_24
                case inl assump_26 =>
                  cases assump_25
                  case intro assump_30 assump_31 =>
                    apply Or.inl
                    apply Or.inl
                    apply Or.inr
                    apply Or.inl
                    apply True.intro
                case inr assump_27 =>
                  cases assump_25
                  case intro assump_38 assump_39 =>
                    apply Or.inl
                    apply Or.inl
                    apply Or.inr
                    apply Or.inl
                    apply True.intro
        case inr assump_9 =>
          apply False.elim assump_9


variable (p4 p5 p1 p6 p3 p2 : Prop)
theorem file28_117546 : ((((((p6 → p6) → (p1 ∨ p6)) → ((True ∨ p2) ∧ (p2 ∧ p1))) ∧ (((p1 ∧ p6) ∧ (p2 → False)) → ((p3 ∨ p4) → (p2 ∨ False)))) ∧ ((((True ∨ False) ∨ (p2 ∧ p2)) ∧ ((p1 → False) → (p1 → p5))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_26 : (((True ∨ False) ∨ (p2 ∧ p2)) ∧ ((p1 → False) → (p1 → p5))) := by
        apply And.intro
        apply Or.inl
        apply Or.inl
        apply True.intro
        intro assump_13
        intro assump_14
        have assump_27 : p1 := by
          exact assump_14
        let assump_19 := assump_13 assump_27
        apply False.elim assump_19
      let assump_12 := assump_3 assump_26
      apply False.elim assump_12


variable (p0 p2 p6 p5 p3 p7 : Prop)
theorem file28_118378 : (((((p2 ∧ p2) → False) ∧ ((p2 → True) → False)) → (((p7 → p7) ∧ (p5 ∧ p3)) ∧ ((p2 ∨ True) ∧ (p2 → False)))) ∨ ((((True ∨ p3) → False) → ((p2 → False) ∧ (p7 → False))) ∧ (((p6 ∨ p0) → False) → False))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    exact assump_2
  apply And.intro
  cases assump_1
  case intro assump_11 assump_12 =>
    have assump_53 : (p2 → True) := by
      intro assump_18
      apply True.intro
    let assump_17 := assump_12 assump_53
    apply False.elim assump_17
  cases assump_1
  case intro assump_22 assump_23 =>
    have assump_54 : (p2 → True) := by
      intro assump_29
      apply True.intro
    let assump_28 := assump_23 assump_54
    apply False.elim assump_28
  apply And.intro
  cases assump_1
  case intro assump_33 assump_34 =>
    apply Or.inr
    apply True.intro
  intro assump_39
  cases assump_1
  case intro assump_42 assump_43 =>
    have assump_55 : (p2 → True) := by
      intro assump_49
      apply True.intro
    let assump_48 := assump_43 assump_55
    apply False.elim assump_48


variable (p1 p4 p5 p2 p7 p3 : Prop)
theorem file28_119572 : (((((p4 ∨ False) ∨ (p2 → True)) ∨ ((True ∨ p3) → False)) → False) → ((((True → True) → (p2 → True)) ∧ ((False → p1) → (p5 → False))) → (((False → p7) → False) → ((p7 → False) → (p1 → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  intro assump_5
  cases assump_2
  case intro assump_12 assump_13 =>
    have assump_25 : (((p4 ∨ False) ∨ (p2 → True)) ∨ ((True ∨ p3) → False)) := by
      apply Or.inl
      apply Or.inr
      intro assump_21
      apply True.intro
    let assump_20 := assump_1 assump_25
    apply False.elim assump_20


variable (p7 p2 p0 p3 p4 p6 p5 p1 : Prop)
theorem file28_120212 : (((((p6 ∧ p1) → (p0 → p7)) ∧ ((p1 ∨ p4) ∧ (p2 ∧ p6))) → (((p0 ∨ p2) → False) → False)) ∨ ((((p2 → False) ∧ (p0 ∧ p5)) → ((p0 ∧ p2) ∧ (p3 ∨ p2))) ∧ (((False ∧ p2) ∨ (p3 ∨ p1)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        cases assump_10
        case intro assump_15 assump_16 =>
          have assump_46 : (p0 ∨ p2) := by
            apply Or.inr
            exact assump_15
          let assump_26 := assump_2 assump_46
          apply False.elim assump_26
      case inr assump_12 =>
        cases assump_10
        case intro assump_32 assump_33 =>
          have assump_47 : (p0 ∨ p2) := by
            apply Or.inr
            exact assump_32
          let assump_42 := assump_2 assump_47
          apply False.elim assump_42


variable (p6 p0 p4 p5 p3 p2 : Prop)
theorem file28_121187 : (((((p6 ∨ p3) ∧ (False ∧ p6)) ∧ ((False ∧ p6) → False)) ∧ (((p4 ∧ p5) → (True → p5)) ∧ ((p2 ∨ True) → (p0 → p5)))) → False) := by
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
            apply False.elim assump_12
        case inr assump_9 =>
          cases assump_7
          case intro assump_18 assump_19 =>
            apply False.elim assump_18


variable (p7 p5 p2 p6 p0 p4 : Prop)
theorem file28_121856 : ((((((True → False) ∧ (p5 ∨ p2)) ∨ ((p4 → True) ∨ (p6 → False))) → (((p7 ∧ p0) ∧ (p2 ∨ False)) → ((p0 ∨ p6) ∨ (p5 → False)))) → False) → False) := by
  intro assump_1
  have assump_42 : ((((True → False) ∧ (p5 ∨ p2)) ∨ ((p4 → True) ∨ (p6 → False))) → (((p7 ∧ p0) ∧ (p2 ∨ False)) → ((p0 ∨ p6) ∨ (p5 → False)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_8
        case inl assump_15 =>
          cases assump_5
          case inl assump_19 =>
            cases assump_19
            case intro assump_21 assump_22 =>
              cases assump_22
              case inl assump_25 =>
                apply Or.inl
                apply Or.inl
                exact assump_10
              case inr assump_26 =>
                apply Or.inl
                apply Or.inl
                exact assump_10
          case inr assump_20 =>
            cases assump_20
            case inl assump_31 =>
              apply Or.inl
              apply Or.inl
              exact assump_10
            case inr assump_32 =>
              apply Or.inl
              apply Or.inl
              exact assump_10
        case inr assump_16 =>
          apply False.elim assump_16
  let assump_4 := assump_1 assump_42
  apply False.elim assump_4


variable (p4 p2 p3 p7 p0 : Prop)
theorem file28_123276 : ((((((p3 → p2) → False) ∨ ((p7 ∨ p4) ∧ (p2 → False))) → (((p0 → False) → False) ∨ ((p0 ∨ p3) ∧ (True → False)))) ∧ ((((False ∨ True) → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : (((False ∨ True) → False) → False) := by
      intro assump_9
      have assump_20 : (False ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_12 := assump_9 assump_20
      apply False.elim assump_12
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


variable (p2 p0 p4 p6 p1 p5 : Prop)
theorem file28_123897 : (((((p6 ∧ False) ∨ (p5 ∨ p1)) → False) ∧ (((p6 ∧ p0) → False) ∧ ((False ∧ p2) ∧ (p1 ∧ p4)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          apply False.elim assump_12


variable (p5 p6 p3 p7 p0 p1 p2 : Prop)
theorem file28_124355 : (((((p5 → False) ∧ (p1 → p6)) ∧ ((False ∧ p5) ∨ (p6 ∨ False))) ∨ (((p6 → False) ∨ (p5 → False)) ∨ ((p2 ∨ False) → (p5 ∨ True)))) → ((((True → False) → False) ∨ ((p7 ∨ p3) → (p6 → False))) ∨ (((p0 ∧ False) → False) ∧ ((True → False) ∧ (p7 → False))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_5
        case inl assump_12 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            apply False.elim assump_14
        case inr assump_13 =>
          cases assump_13
          case inl assump_18 =>
            apply Or.inl
            apply Or.inl
            intro assump_22
            have assump_62 : True := by
              apply True.intro
            let assump_25 := assump_22 assump_62
            apply False.elim assump_25
          case inr assump_19 =>
            apply False.elim assump_19
  case inr assump_3 =>
    cases assump_3
    case inl assump_31 =>
      cases assump_31
      case inl assump_33 =>
        apply Or.inl
        apply Or.inl
        intro assump_37
        have assump_63 : True := by
          apply True.intro
        let assump_40 := assump_37 assump_63
        apply False.elim assump_40
      case inr assump_34 =>
        apply Or.inl
        apply Or.inl
        intro assump_46
        have assump_64 : True := by
          apply True.intro
        let assump_49 := assump_46 assump_64
        apply False.elim assump_49
    case inr assump_32 =>
      apply Or.inl
      apply Or.inl
      intro assump_55
      have assump_65 : True := by
        apply True.intro
      let assump_58 := assump_55 assump_65
      apply False.elim assump_58


variable (p3 p1 p6 p7 p4 p5 p2 : Prop)
theorem file28_126189 : ((((((False → False) → False) → ((p4 ∨ p4) → False)) ∧ (((p5 → p3) → False) ∧ ((p5 ∧ True) → (p3 ∧ p2)))) ∧ ((((p1 → False) ∧ (p4 ∧ p6)) ∧ ((p7 ∧ p3) → (False ∧ p5))) ∨ (((p3 ∧ p3) ∨ (p3 ∧ True)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_3
        case inl assump_14 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              cases assump_19
              case intro assump_22 assump_23 =>
                have assump_66 : (p5 → p3) := by
                  intro assump_36
                  have assump_67 : (p5 ∧ True) := by
                    apply And.intro
                    exact assump_36
                    apply True.intro
                  let assump_44 := assump_9 assump_67
                  let assump_45 := And.left assump_44
                  exact assump_45
                let assump_35 := assump_8 assump_66
                apply False.elim assump_35
        case inr assump_15 =>
          have assump_68 : (p5 → p3) := by
            intro assump_55
            have assump_69 : (p5 ∧ True) := by
              apply And.intro
              exact assump_55
              apply True.intro
            let assump_60 := assump_9 assump_69
            let assump_61 := And.left assump_60
            exact assump_61
          let assump_54 := assump_8 assump_68
          apply False.elim assump_54


variable (p6 p5 p2 p0 p1 p7 p3 p4 : Prop)
theorem file28_127862 : ((((((p0 → p5) ∧ (True → p6)) ∧ ((False ∧ p6) ∧ (p0 → p7))) ∧ (((p0 ∨ p2) ∧ (p1 → False)) ∧ ((p7 → p3) → False))) ∧ ((((p0 ∧ p7) → False) → ((p6 → p7) ∧ (p3 ∨ p1))) → (((p1 → p1) → (p1 ∧ p0)) ∧ ((p7 ∧ p1) ∧ (p4 ∧ p6))))) → False) := by
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
          case intro assump_14 assump_15 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              apply False.elim assump_16


variable (p7 p5 p3 p4 : Prop)
theorem file28_128581 : ((((((p3 ∨ False) → False) → False) → (((p7 → False) ∧ (p4 ∨ p3)) → False)) ∧ ((((False ∧ p4) ∧ (False → p5)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : (((False ∧ p4) ∧ (False → p5)) → False) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          apply False.elim assump_12
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


variable (p6 p2 p7 p3 p5 p1 : Prop)
theorem file28_129174 : (((((False → p6) ∨ (p5 → False)) → False) ∨ (((p2 → False) ∨ (False ∧ p7)) ∧ ((p1 ∨ p2) → False))) → ((((p6 ∨ p3) → False) → ((p3 ∧ p1) ∨ (p3 ∨ True))) ∧ (((p7 ∧ p1) → False) ∨ ((p5 ∨ False) → False)))) := by
  intro assump_5
  apply And.intro
  intro assump_6
  cases assump_5
  case inl assump_9 =>
    apply Or.inr
    apply Or.inr
    apply True.intro
  case inr assump_10 =>
    cases assump_10
    case intro assump_13 assump_14 =>
      cases assump_13
      case inl assump_15 =>
        apply Or.inr
        apply Or.inr
        apply True.intro
      case inr assump_16 =>
        cases assump_16
        case intro assump_21 assump_22 =>
          apply False.elim assump_21
  cases assump_5
  case inl assump_25 =>
    apply Or.inl
    intro assump_29
    cases assump_29
    case intro assump_30 assump_31 =>
      have assump_70 : ((False → p6) ∨ (p5 → False)) := by
        apply Or.inl
        intro assump_39
        apply False.elim assump_39
      let assump_38 := assump_25 assump_70
      apply False.elim assump_38
  case inr assump_26 =>
    cases assump_26
    case intro assump_45 assump_46 =>
      cases assump_45
      case inl assump_47 =>
        apply Or.inl
        intro assump_53
        cases assump_53
        case intro assump_54 assump_55 =>
          have assump_71 : (p1 ∨ p2) := by
            apply Or.inl
            exact assump_55
          let assump_62 := assump_46 assump_71
          apply False.elim assump_62
      case inr assump_48 =>
        cases assump_48
        case intro assump_66 assump_67 =>
          apply False.elim assump_66


