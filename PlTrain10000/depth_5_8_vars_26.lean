variable (p6 p1 p2 p0 p3 p4 : Prop)
theorem file26_44 : ((((((p6 → False) → (False → False)) ∨ ((p3 ∨ True) ∧ (p6 ∧ p4))) → (((p0 ∧ p2) → (p3 → False)) ∧ ((p6 ∧ False) ∧ (p0 → p1)))) ∨ ((((p4 → True) → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_33 : (((p6 → False) → (False → False)) ∨ ((p3 ∨ True) ∧ (p6 ∧ p4))) := by
      apply Or.inl
      intro assump_7
      intro assump_8
      apply False.elim assump_8
    let assump_6 := assump_2 assump_33
    let assump_11 := And.right assump_6
    let assump_13 := And.left assump_11
    let assump_14 := And.right assump_13
    apply False.elim assump_14
  case inr assump_3 =>
    have assump_34 : (((p4 → True) → False) → False) := by
      intro assump_22
      have assump_35 : (p4 → True) := by
        intro assump_26
        apply True.intro
      let assump_25 := assump_22 assump_35
      apply False.elim assump_25
    let assump_21 := assump_3 assump_34
    apply False.elim assump_21


variable (p0 p1 p5 p4 p7 p3 : Prop)
theorem file26_1063 : (((((True ∨ True) → (p3 → p5)) ∨ ((False → False) → (False ∧ p3))) ∧ (((p7 ∨ p1) ∨ (p0 → False)) ∧ ((p4 → p4) → False))) → ((((p0 ∨ p4) → (p3 ∨ p4)) → False) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      cases assump_6
      case intro assump_11 assump_12 =>
        cases assump_11
        case inl assump_13 =>
          cases assump_13
          case inl assump_15 =>
            have assump_91 : (p4 → p4) := by
              intro assump_22
              exact assump_22
            let assump_21 := assump_12 assump_91
            apply False.elim assump_21
          case inr assump_16 =>
            have assump_92 : (p4 → p4) := by
              intro assump_33
              exact assump_33
            let assump_32 := assump_12 assump_92
            apply False.elim assump_32
        case inr assump_14 =>
          have assump_93 : (p4 → p4) := by
            intro assump_44
            exact assump_44
          let assump_43 := assump_12 assump_93
          apply False.elim assump_43
    case inr assump_8 =>
      cases assump_6
      case intro assump_52 assump_53 =>
        cases assump_52
        case inl assump_54 =>
          cases assump_54
          case inl assump_56 =>
            have assump_94 : (p4 → p4) := by
              intro assump_63
              exact assump_63
            let assump_62 := assump_53 assump_94
            apply False.elim assump_62
          case inr assump_57 =>
            have assump_95 : (p4 → p4) := by
              intro assump_74
              exact assump_74
            let assump_73 := assump_53 assump_95
            apply False.elim assump_73
        case inr assump_55 =>
          have assump_96 : (p4 → p4) := by
            intro assump_85
            exact assump_85
          let assump_84 := assump_53 assump_96
          apply False.elim assump_84


variable (p6 p2 : Prop)
theorem file26_3047 : (((((True ∨ False) ∨ (False ∨ p2)) ∨ ((p2 ∨ p6) → False)) → False) → False) := by
  intro assump_1
  have assump_8 : (((True ∨ False) ∨ (False ∨ p2)) ∨ ((p2 ∨ p6) → False)) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p3 p6 p7 p1 p4 p0 p2 : Prop)
theorem file26_3425 : (((((p2 → False) → (p2 → p3)) ∨ ((p2 → p0) ∧ (p2 → False))) ∨ (((p4 → p3) ∨ (p7 → p6)) ∧ ((p0 ∧ p3) → False))) ∨ ((((p7 ∨ p1) ∨ (p7 ∧ p4)) → ((p6 → p7) → (p2 ∨ p2))) ∧ (((p2 ∧ p7) → (p3 → False)) ∨ ((p7 ∧ p6) → False)))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  have assump_11 : p2 := by
    exact assump_2
  let assump_7 := assump_1 assump_11
  apply False.elim assump_7


variable (p3 p0 p2 p6 p1 p7 p5 : Prop)
theorem file26_3906 : (((((p3 ∧ p6) ∧ (p1 ∨ p5)) ∧ ((p1 → p5) ∧ (p2 ∨ p0))) ∧ (((p1 → False) ∧ (p6 → False)) → ((p3 → False) → (p0 ∧ p6)))) → ((((p7 → False) ∨ (p3 ∧ p0)) → ((p3 → p0) → (p3 → p3))) ∨ (((True ∧ p1) ∧ (True ∧ p3)) → False))) := by
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
              case inl assump_22 =>
                apply Or.inl
                intro assump_28
                intro assump_29
                intro assump_30
                cases assump_28
                case inl assump_35 =>
                  exact assump_30
                case inr assump_36 =>
                  cases assump_36
                  case intro assump_39 assump_40 =>
                    exact assump_39
              case inr assump_23 =>
                apply Or.inl
                intro assump_49
                intro assump_50
                intro assump_51
                cases assump_49
                case inl assump_56 =>
                  exact assump_51
                case inr assump_57 =>
                  cases assump_57
                  case intro assump_60 assump_61 =>
                    exact assump_60
          case inr assump_15 =>
            cases assump_5
            case intro assump_68 assump_69 =>
              cases assump_69
              case inl assump_72 =>
                apply Or.inl
                intro assump_78
                intro assump_79
                intro assump_80
                cases assump_78
                case inl assump_85 =>
                  exact assump_80
                case inr assump_86 =>
                  cases assump_86
                  case intro assump_89 assump_90 =>
                    exact assump_89
              case inr assump_73 =>
                apply Or.inl
                intro assump_99
                intro assump_100
                intro assump_101
                cases assump_99
                case inl assump_106 =>
                  exact assump_101
                case inr assump_107 =>
                  cases assump_107
                  case intro assump_110 assump_111 =>
                    exact assump_110


variable (p6 p4 p7 p1 : Prop)
theorem file26_6433 : (((((p4 → False) ∨ (p4 → False)) ∧ ((p6 ∨ p7) → (p1 → True))) ∧ (((False ∧ False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        have assump_38 : ((False ∧ False) → False) := by
          intro assump_15
          cases assump_15
          case intro assump_16 assump_17 =>
            apply False.elim assump_16
        let assump_14 := assump_3 assump_38
        apply False.elim assump_14
      case inr assump_7 =>
        have assump_39 : ((False ∧ False) → False) := by
          intro assump_30
          cases assump_30
          case intro assump_31 assump_32 =>
            apply False.elim assump_31
        let assump_29 := assump_3 assump_39
        apply False.elim assump_29


variable (p2 p1 p0 : Prop)
theorem file26_7340 : (((((True ∨ p0) ∨ (False → False)) → False) → False) ∨ ((((p0 → True) → (True ∨ True)) ∧ ((p2 → p1) ∨ (False → False))) ∨ (((True → False) → False) → False))) := by
  apply Or.inl
  intro assump_1
  have assump_8 : ((True ∨ p0) ∨ (False → False)) := by
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


theorem file26_7736 : (((((False → False) → False) → False) → False) → False) := by
  intro assump_1
  have assump_18 : (((False → False) → False) → False) := by
    intro assump_5
    have assump_19 : (False → False) := by
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p6 p3 p2 p0 p7 p1 p5 p4 : Prop)
theorem file26_8191 : (((((p7 ∨ p2) → False) → False) → (((p1 → False) → (p4 ∨ p7)) → ((p3 ∨ p5) → (p1 ∨ True)))) ∨ ((((p7 → p2) → False) → ((p3 → p0) ∧ (p6 → False))) ∧ (((p6 → False) → False) ∧ ((p0 → False) → (p7 ∨ True))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    apply Or.inr
    apply True.intro
  case inr assump_5 =>
    apply Or.inr
    apply True.intro


variable (p6 p3 p2 p7 p4 p1 : Prop)
theorem file26_8668 : ((((((True → False) ∧ (p2 → False)) → ((p3 ∨ p7) → False)) ∨ (((False → False) ∨ (p3 ∧ p3)) → False)) ∧ ((((p4 ∨ p6) ∨ (p4 → p2)) ∨ ((p4 ∨ p1) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_38 : (((p4 ∨ p6) ∨ (p4 → p2)) ∨ ((p4 ∨ p1) → False)) := by
        apply Or.inl
        apply Or.inr
        intro assump_11
        have assump_39 : (((p4 ∨ p6) ∨ (p4 → p2)) ∨ ((p4 ∨ p1) → False)) := by
          apply Or.inl
          apply Or.inl
          apply Or.inl
          exact assump_11
        let assump_15 := assump_3 assump_39
        apply False.elim assump_15
      let assump_10 := assump_3 assump_38
      apply False.elim assump_10
    case inr assump_5 =>
      have assump_40 : (((p4 ∨ p6) ∨ (p4 → p2)) ∨ ((p4 ∨ p1) → False)) := by
        apply Or.inl
        apply Or.inr
        intro assump_27
        have assump_41 : (((p4 ∨ p6) ∨ (p4 → p2)) ∨ ((p4 ∨ p1) → False)) := by
          apply Or.inl
          apply Or.inl
          apply Or.inl
          exact assump_27
        let assump_31 := assump_3 assump_41
        apply False.elim assump_31
      let assump_26 := assump_3 assump_40
      apply False.elim assump_26


variable (p0 p2 p1 p4 p7 p5 : Prop)
theorem file26_9985 : (((((False → p2) → (True → False)) ∧ ((False ∨ p0) → (p5 ∧ p4))) → (((p2 ∨ p0) ∨ (True → False)) ∧ ((False ∨ p2) → (p0 → False)))) ∧ ((((False → False) ∨ (False → True)) → False) → (((p7 ∧ p0) ∧ (p7 → False)) ∨ ((p1 → False) → False)))) := by
  apply And.intro
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inr
    intro assump_8
    have assump_62 : (False → p2) := by
      intro assump_13
      apply False.elim assump_13
    let assump_12 := assump_2 assump_62
    have assump_63 : True := by
      apply True.intro
    let assump_16 := assump_12 assump_63
    apply False.elim assump_16
  intro assump_20
  intro assump_21
  cases assump_20
  case inl assump_24 =>
    apply False.elim assump_24
  case inr assump_25 =>
    cases assump_1
    case intro assump_30 assump_31 =>
      have assump_64 : (False → p2) := by
        intro assump_41
        apply False.elim assump_41
      let assump_40 := assump_30 assump_64
      have assump_65 : True := by
        apply True.intro
      let assump_44 := assump_40 assump_65
      apply False.elim assump_44
  intro assump_48
  apply Or.inr
  intro assump_51
  have assump_66 : ((False → False) ∨ (False → True)) := by
    apply Or.inl
    intro assump_56
    apply False.elim assump_56
  let assump_55 := assump_48 assump_66
  apply False.elim assump_55


variable (p0 p6 p1 p5 : Prop)
theorem file26_11400 : ((((((False ∧ p5) → False) → False) → (((p1 → p5) → (p0 → False)) ∧ ((p0 → p6) → (p5 → p0)))) → False) → False) := by
  intro assump_1
  have assump_43 : ((((False ∧ p5) → False) → False) → (((p1 → p5) → (p0 → False)) ∧ ((p0 → p6) → (p5 → p0)))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    intro assump_7
    have assump_44 : ((False ∧ p5) → False) := by
      intro assump_15
      cases assump_15
      case intro assump_16 assump_17 =>
        apply False.elim assump_16
    let assump_14 := assump_5 assump_44
    apply False.elim assump_14
    intro assump_23
    intro assump_24
    have assump_45 : ((False ∧ p5) → False) := by
      intro assump_32
      cases assump_32
      case intro assump_33 assump_34 =>
        apply False.elim assump_33
    let assump_31 := assump_5 assump_45
    apply False.elim assump_31
  let assump_4 := assump_1 assump_43
  apply False.elim assump_4


variable (p1 p5 p0 p6 p2 p4 p3 : Prop)
theorem file26_12377 : (((((p2 ∧ p5) ∨ (p4 → True)) → False) → False) ∨ ((((p5 ∨ p2) → (p6 → False)) ∨ ((p5 → False) ∨ (p0 → False))) → (((p3 ∧ p4) ∨ (p1 → True)) → False))) := by
  apply Or.inl
  intro assump_1
  have assump_9 : ((p2 ∧ p5) ∨ (p4 → True)) := by
    apply Or.inr
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_9
  apply False.elim assump_4


variable (p1 p5 p6 p7 p4 p3 p2 : Prop)
theorem file26_12800 : (((((p6 ∨ True) ∨ (False ∧ p3)) ∨ ((p6 → p6) ∨ (p6 → False))) ∧ (((p4 ∧ False) → False) ∨ ((True → p4) ∧ (False ∧ p1)))) ∨ ((((p2 ∧ p5) → False) ∧ ((p7 ∨ p7) → False)) → False)) := by
  apply Or.inl
  apply And.intro
  apply Or.inl
  apply Or.inl
  apply Or.inr
  apply True.intro
  apply Or.inl
  intro assump_26
  cases assump_26
  case intro assump_27 assump_28 =>
    apply False.elim assump_28


variable (p4 p1 p3 p6 p2 p7 : Prop)
theorem file26_13259 : ((((((p7 ∧ p6) → (p4 ∧ False)) ∨ ((p6 ∨ p4) ∧ (p3 → False))) ∧ (((p1 → False) ∨ (p1 ∨ p7)) ∧ ((p2 ∧ p4) ∧ (False ∧ True)))) ∧ ((((p4 → False) → (True ∨ p6)) → False) → (((p7 → p2) ∨ (p4 → False)) ∧ ((True → False) → (p2 ∨ p1))))) → False) := by
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
              cases assump_16
              case intro assump_18 assump_19 =>
                cases assump_17
                case intro assump_24 assump_25 =>
                  apply False.elim assump_24
          case inr assump_13 =>
            cases assump_13
            case inl assump_28 =>
              cases assump_11
              case intro assump_32 assump_33 =>
                cases assump_32
                case intro assump_34 assump_35 =>
                  cases assump_33
                  case intro assump_40 assump_41 =>
                    apply False.elim assump_40
            case inr assump_29 =>
              cases assump_11
              case intro assump_46 assump_47 =>
                cases assump_46
                case intro assump_48 assump_49 =>
                  cases assump_47
                  case intro assump_54 assump_55 =>
                    apply False.elim assump_54
      case inr assump_7 =>
        cases assump_7
        case intro assump_58 assump_59 =>
          cases assump_58
          case inl assump_60 =>
            cases assump_5
            case intro assump_66 assump_67 =>
              cases assump_66
              case inl assump_68 =>
                cases assump_67
                case intro assump_72 assump_73 =>
                  cases assump_72
                  case intro assump_74 assump_75 =>
                    cases assump_73
                    case intro assump_80 assump_81 =>
                      apply False.elim assump_80
              case inr assump_69 =>
                cases assump_69
                case inl assump_84 =>
                  cases assump_67
                  case intro assump_88 assump_89 =>
                    cases assump_88
                    case intro assump_90 assump_91 =>
                      cases assump_89
                      case intro assump_96 assump_97 =>
                        apply False.elim assump_96
                case inr assump_85 =>
                  cases assump_67
                  case intro assump_102 assump_103 =>
                    cases assump_102
                    case intro assump_104 assump_105 =>
                      cases assump_103
                      case intro assump_110 assump_111 =>
                        apply False.elim assump_110
          case inr assump_61 =>
            cases assump_5
            case intro assump_118 assump_119 =>
              cases assump_118
              case inl assump_120 =>
                cases assump_119
                case intro assump_124 assump_125 =>
                  cases assump_124
                  case intro assump_126 assump_127 =>
                    cases assump_125
                    case intro assump_132 assump_133 =>
                      apply False.elim assump_132
              case inr assump_121 =>
                cases assump_121
                case inl assump_136 =>
                  cases assump_119
                  case intro assump_140 assump_141 =>
                    cases assump_140
                    case intro assump_142 assump_143 =>
                      cases assump_141
                      case intro assump_148 assump_149 =>
                        apply False.elim assump_148
                case inr assump_137 =>
                  cases assump_119
                  case intro assump_154 assump_155 =>
                    cases assump_154
                    case intro assump_156 assump_157 =>
                      cases assump_155
                      case intro assump_162 assump_163 =>
                        apply False.elim assump_162


variable (p2 p5 p3 p4 : Prop)
theorem file26_17538 : ((((((p2 ∨ p2) ∧ (p4 → False)) → ((p2 → False) → (p5 → False))) ∨ (((p3 → False) ∧ (False → False)) → False)) → False) → False) := by
  intro assump_1
  have assump_39 : ((((p2 ∨ p2) ∧ (p4 → False)) → ((p2 → False) → (p5 → False))) ∨ (((p3 → False) ∧ (False → False)) → False)) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_5
    case intro assump_12 assump_13 =>
      cases assump_12
      case inl assump_14 =>
        have assump_40 : p2 := by
          exact assump_14
        let assump_22 := assump_6 assump_40
        apply False.elim assump_22
      case inr assump_15 =>
        have assump_41 : p2 := by
          exact assump_15
        let assump_32 := assump_6 assump_41
        apply False.elim assump_32
  let assump_4 := assump_1 assump_39
  apply False.elim assump_4


variable (p1 p4 p5 p2 p0 p7 : Prop)
theorem file26_18434 : (((((True ∨ True) ∨ (p1 ∧ p4)) → False) → (((p0 → p0) → (p2 → False)) ∨ ((p1 → False) → (p2 ∧ p5)))) ∨ ((((p2 → p2) → False) → ((p0 ∧ p7) ∨ (p7 ∧ p0))) → (((p2 ∧ p4) → False) → False))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  have assump_16 : ((True ∨ True) ∨ (p1 ∧ p4)) := by
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_12 := assump_1 assump_16
  apply False.elim assump_12


variable (p5 p0 p2 p7 p4 p1 p6 : Prop)
theorem file26_18945 : (((((False ∧ p5) → False) ∨ ((p0 → False) ∧ (p1 ∨ p6))) ∨ (((p5 → p0) ∨ (p7 → p4)) ∨ ((True ∨ p6) → (False → False)))) ∧ ((((p6 → False) ∧ (p4 ∧ True)) ∧ ((p7 ∨ p0) → False)) → (((p7 ∨ False) → (p6 → False)) ∨ ((p2 ∨ p7) ∨ (p1 ∧ p7))))) := by
  apply And.intro
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply False.elim assump_2
  intro assump_6
  cases assump_6
  case intro assump_7 assump_8 =>
    cases assump_7
    case intro assump_9 assump_10 =>
      cases assump_10
      case intro assump_13 assump_14 =>
        apply Or.inl
        intro assump_21
        intro assump_22
        cases assump_21
        case inl assump_25 =>
          have assump_37 : (p7 ∨ p0) := by
            apply Or.inl
            exact assump_25
          let assump_31 := assump_8 assump_37
          apply False.elim assump_31
        case inr assump_26 =>
          apply False.elim assump_26


variable (p2 p6 p7 p5 p3 p4 : Prop)
theorem file26_19949 : ((((((p6 ∧ p2) ∨ (p6 → False)) → ((True ∧ p2) ∨ (p3 → p5))) → (((p5 ∧ p2) ∧ (p2 ∧ p2)) → ((p2 ∧ p2) ∨ (p4 → p7)))) → False) → False) := by
  intro assump_1
  have assump_26 : ((((p6 ∧ p2) ∨ (p6 → False)) → ((True ∧ p2) ∨ (p3 → p5))) → (((p5 ∧ p2) ∧ (p2 ∧ p2)) → ((p2 ∧ p2) ∨ (p4 → p7)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_8
        case intro assump_15 assump_16 =>
          apply Or.inl
          apply And.intro
          exact assump_16
          exact assump_16
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p5 p6 p3 p4 p0 p2 p7 : Prop)
theorem file26_20690 : (((((p4 → p3) → (True → False)) → False) ∨ (((p6 ∧ p2) → (p3 → p2)) ∧ ((p5 ∧ p0) → False))) → ((((p7 ∧ True) → False) → ((p0 ∨ p7) ∨ (False → False))) ∨ (((p3 ∨ p2) ∧ (p5 → p2)) → False))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    apply Or.inr
    intro assump_9
    apply False.elim assump_9
  case inr assump_3 =>
    cases assump_3
    case intro assump_12 assump_13 =>
      apply Or.inl
      intro assump_18
      apply Or.inr
      intro assump_21
      apply False.elim assump_21


variable (p6 p4 p3 p2 p0 p7 p5 p1 : Prop)
theorem file26_21305 : (((((p0 ∧ p6) → (p4 → p2)) → ((True → False) → False)) ∨ (((True → p1) → (True ∨ True)) ∧ ((p2 ∧ p1) → (p0 ∨ p4)))) ∨ ((((p0 → False) → (p0 → False)) ∧ ((p4 → True) ∨ (p3 → p1))) ∨ (((p5 ∨ p5) ∨ (p4 → p1)) ∨ ((p1 ∧ p7) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  have assump_12 : True := by
    apply True.intro
  let assump_8 := assump_2 assump_12
  apply False.elim assump_8


variable (p1 p5 p4 p7 p6 p2 p3 : Prop)
theorem file26_21785 : (((((True ∧ p3) ∨ (p3 → False)) → False) → (((False → p6) ∨ (p4 ∨ p6)) ∨ ((p1 ∧ p3) ∧ (p3 ∨ p4)))) → ((((p3 → False) ∧ (p5 ∨ True)) → ((p3 → False) → (p7 ∨ p6))) → (((False ∧ p2) ∧ (p7 → False)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_4
    case intro assump_6 assump_7 =>
      apply False.elim assump_6


variable (p2 p5 p0 p1 p7 : Prop)
theorem file26_22243 : ((((((False ∧ p1) → False) ∨ ((p0 ∧ p1) → False)) ∧ (((p7 ∨ True) → False) → ((p5 → False) ∨ (p0 ∨ p2)))) → False) → False) := by
  intro assump_1
  have assump_24 : ((((False ∧ p1) → False) ∨ ((p0 ∧ p1) → False)) ∧ (((p7 ∨ True) → False) → ((p5 → False) ∨ (p0 ∨ p2)))) := by
    apply And.intro
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
    intro assump_10
    apply Or.inl
    intro assump_13
    have assump_25 : (p7 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_17 := assump_10 assump_25
    apply False.elim assump_17
  let assump_4 := assump_1 assump_24
  apply False.elim assump_4


variable (p1 p7 p6 p0 p3 p4 : Prop)
theorem file26_22997 : ((((((p4 → False) → (p7 → p1)) → ((True ∨ p4) ∧ (p7 → True))) ∨ (((p6 ∧ p7) → (p1 ∧ True)) ∧ ((p0 → p1) ∧ (p3 ∨ True)))) → False) → False) := by
  intro assump_1
  have assump_12 : ((((p4 → False) → (p7 → p1)) → ((True ∨ p4) ∧ (p7 → True))) ∨ (((p6 ∧ p7) → (p1 ∧ True)) ∧ ((p0 → p1) ∧ (p3 ∨ True)))) := by
    apply Or.inl
    intro assump_5
    apply And.intro
    apply Or.inl
    apply True.intro
    intro assump_8
    apply True.intro
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p2 p0 p5 p3 p1 p6 p7 p4 : Prop)
theorem file26_23568 : (((((False ∧ p4) → (False ∨ p6)) → False) → (((p5 → p4) ∧ (p7 → p1)) → False)) ∨ ((((True → False) ∨ (p0 ∨ p3)) ∨ ((p3 → False) ∧ (p3 ∨ p5))) → (((p4 ∧ False) → False) ∨ ((True ∨ p3) ∨ (p2 ∨ False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    have assump_20 : ((False ∧ p4) → (False ∨ p6)) := by
      intro assump_12
      cases assump_12
      case intro assump_13 assump_14 =>
        apply False.elim assump_13
    let assump_11 := assump_1 assump_20
    apply False.elim assump_11


variable (p2 p6 p1 p0 p4 p5 p7 p3 : Prop)
theorem file26_24189 : (((((p5 ∧ False) ∨ (False ∧ p1)) ∧ ((p2 ∧ p1) ∧ (p1 → p3))) ∧ (((p2 → False) ∧ (p3 → p2)) → ((p5 ∧ p1) ∨ (p7 → p6)))) → ((((p4 → p0) ∨ (p7 → p4)) → False) ∨ (((p2 → False) → False) ∧ ((p1 ∧ False) → False)))) := by
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    cases assump_10
    case intro assump_12 assump_13 =>
      cases assump_12
      case inl assump_14 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          apply False.elim assump_17
      case inr assump_15 =>
        cases assump_15
        case intro assump_22 assump_23 =>
          apply False.elim assump_22


variable (p7 p3 p0 p5 p2 p1 : Prop)
theorem file26_24876 : (((((p3 → p7) → False) → False) → False) → ((((p1 ∧ p5) ∨ (p7 ∧ True)) ∨ ((p2 ∧ p7) → False)) ∧ (((False → False) ∨ (p2 → False)) → ((False → False) ∨ (False → p0))))) := by
  intro assump_1
  apply And.intro
  apply Or.inr
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    have assump_44 : (((p3 → p7) → False) → False) := by
      intro assump_14
      have assump_45 : (p3 → p7) := by
        intro assump_18
        exact assump_6
      let assump_17 := assump_14 assump_45
      apply False.elim assump_17
    let assump_13 := assump_1 assump_44
    apply False.elim assump_13
  intro assump_27
  cases assump_27
  case inl assump_28 =>
    apply Or.inl
    intro assump_34
    apply False.elim assump_34
  case inr assump_29 =>
    apply Or.inl
    intro assump_41
    apply False.elim assump_41


variable (p6 p3 p4 p5 p2 : Prop)
theorem file26_25757 : ((((((p2 → True) → False) ∧ ((p4 ∨ p3) → False)) → (((p5 → False) ∧ (False → False)) ∧ ((p6 → False) → False))) → False) → False) := by
  intro assump_14
  have assump_55 : ((((p2 → True) → False) ∧ ((p4 ∨ p3) → False)) → (((p5 → False) ∧ (False → False)) ∧ ((p6 → False) → False))) := by
    intro assump_18
    apply And.intro
    apply And.intro
    intro assump_19
    cases assump_18
    case intro assump_22 assump_23 =>
      have assump_56 : (p2 → True) := by
        intro assump_30
        apply True.intro
      let assump_29 := assump_22 assump_56
      apply False.elim assump_29
    intro assump_34
    apply False.elim assump_34
    intro assump_37
    cases assump_18
    case intro assump_40 assump_41 =>
      have assump_57 : (p2 → True) := by
        intro assump_48
        apply True.intro
      let assump_47 := assump_40 assump_57
      apply False.elim assump_47
  let assump_17 := assump_14 assump_55
  apply False.elim assump_17


variable (p1 p2 p7 p0 p4 p3 : Prop)
theorem file26_26773 : ((((((p1 ∧ p3) ∧ (p0 ∨ True)) → False) → (((p4 ∨ p2) ∨ (False ∨ p7)) ∨ ((p2 → False) ∨ (p1 ∧ False)))) → False) → False) := by
  intro assump_9
  have assump_31 : ((((p1 ∧ p3) ∧ (p0 ∨ True)) → False) → (((p4 ∨ p2) ∨ (False ∨ p7)) ∨ ((p2 → False) ∨ (p1 ∧ False)))) := by
    intro assump_13
    apply Or.inr
    apply Or.inl
    intro assump_16
    have assump_32 : ((((p1 ∧ p3) ∧ (p0 ∨ True)) → False) → (((p4 ∨ p2) ∨ (False ∨ p7)) ∨ ((p2 → False) ∨ (p1 ∧ False)))) := by
      intro assump_22
      apply Or.inl
      apply Or.inl
      apply Or.inr
      exact assump_16
    let assump_21 := assump_9 assump_32
    apply False.elim assump_21
  let assump_12 := assump_9 assump_31
  apply False.elim assump_12


variable (p4 p5 p3 p7 : Prop)
theorem file26_27538 : ((((((p7 → False) → (p7 → p3)) → ((True → False) ∧ (p4 → p4))) → (((p3 ∨ p7) → (p5 ∧ p7)) → False)) → False) → False) := by
  intro assump_1
  have assump_30 : ((((p7 → False) → (p7 → p3)) → ((True → False) ∧ (p4 → p4))) → (((p3 ∨ p7) → (p5 ∧ p7)) → False)) := by
    intro assump_5
    intro assump_6
    have assump_31 : ((p7 → False) → (p7 → p3)) := by
      intro assump_12
      intro assump_13
      have assump_32 : p7 := by
        exact assump_13
      let assump_18 := assump_12 assump_32
      apply False.elim assump_18
    let assump_11 := assump_5 assump_31
    let assump_22 := And.left assump_11
    have assump_33 : True := by
      apply True.intro
    let assump_23 := assump_22 assump_33
    apply False.elim assump_23
  let assump_4 := assump_1 assump_30
  apply False.elim assump_4


variable (p2 p4 p6 p5 p0 p7 : Prop)
theorem file26_28402 : (((((p4 → p2) → False) → ((p7 ∧ p5) ∨ (False → p5))) ∨ (((p5 → False) ∧ (p6 → p5)) → False)) ∨ ((((False ∨ False) ∧ (p2 → False)) ∧ ((p5 → False) ∨ (True → p0))) → (((p0 → p5) → False) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inr
  intro assump_4
  apply False.elim assump_4


variable (p1 p7 p2 p3 p5 p0 p6 : Prop)
theorem file26_28774 : ((((((p1 → p3) ∧ (p6 ∨ p0)) → ((p5 → False) ∨ (p0 → p1))) → False) ∧ ((((p3 → False) → (p2 → p1)) ∧ ((True ∧ p0) → False)) ∧ (((False ∧ p6) → (p7 → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        have assump_28 : ((False ∧ p6) → (p7 → False)) := by
          intro assump_17
          intro assump_18
          cases assump_17
          case intro assump_21 assump_22 =>
            apply False.elim assump_21
        let assump_16 := assump_7 assump_28
        apply False.elim assump_16


variable (p3 p0 p7 p2 p5 : Prop)
theorem file26_29496 : (((((p3 → False) → False) ∨ ((p5 → False) → (False ∨ True))) → (((p0 ∨ False) → (p7 ∨ p0)) ∨ ((p2 ∨ p5) → (p3 ∧ p5)))) ∨ ((((False → False) → False) → False) ∧ (((True → False) → False) ∨ ((p3 ∧ p2) → False)))) := by
  apply Or.inl
  intro assump_9
  cases assump_9
  case inl assump_10 =>
    apply Or.inl
    intro assump_14
    cases assump_14
    case inl assump_15 =>
      apply Or.inr
      exact assump_15
    case inr assump_16 =>
      apply False.elim assump_16
  case inr assump_11 =>
    apply Or.inl
    intro assump_23
    cases assump_23
    case inl assump_24 =>
      apply Or.inr
      exact assump_24
    case inr assump_25 =>
      apply False.elim assump_25


variable (p3 p7 p5 p1 p0 p6 : Prop)
theorem file26_30236 : ((((((p0 ∨ p7) ∨ (True ∨ p6)) ∨ ((p5 ∧ False) → False)) ∨ (((p3 → False) → (p5 → True)) ∨ ((False ∨ p7) ∨ (False ∨ p1)))) → False) → False) := by
  intro assump_5
  have assump_12 : ((((p0 ∨ p7) ∨ (True ∨ p6)) ∨ ((p5 ∧ False) → False)) ∨ (((p3 → False) → (p5 → True)) ∨ ((False ∨ p7) ∨ (False ∨ p1)))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply Or.inl
    apply True.intro
  let assump_8 := assump_5 assump_12
  apply False.elim assump_8


variable (p5 p3 : Prop)
theorem file26_30746 : ((((((p3 ∧ True) → False) → False) → False) ∧ ((((p3 ∨ p5) → (p5 ∨ p5)) → ((True → False) → (False → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_17 : (((p3 ∨ p5) → (p5 ∨ p5)) → ((True → False) → (False → False))) := by
      intro assump_9
      intro assump_10
      intro assump_11
      apply False.elim assump_11
    let assump_8 := assump_3 assump_17
    apply False.elim assump_8


variable (p7 p1 p2 p0 p5 p4 p3 : Prop)
theorem file26_31269 : (((((p5 ∨ False) ∨ (p5 ∧ True)) ∧ ((p0 → False) ∧ (p7 ∧ p2))) ∨ (((True ∧ False) → (p7 → False)) ∨ ((p4 → p2) → False))) ∨ ((((p3 → p0) → False) → ((p3 → False) ∨ (p1 → p4))) ∧ (((p2 ∨ p2) → False) → ((p4 → False) → False)))) := by
  apply Or.inl
  apply Or.inr
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    apply False.elim assump_6


variable (p3 p2 p6 p0 p7 p5 p4 : Prop)
theorem file26_31724 : (((((p5 ∧ p4) ∧ (p5 ∧ p6)) ∧ ((p6 ∧ p5) ∧ (True → False))) ∧ (((p7 ∨ False) → (p0 → p7)) ∧ ((p3 → True) → False))) ∨ ((((True ∧ p2) → (p3 → False)) ∨ ((p6 ∧ p5) → (False → False))) → (((p6 ∧ p7) ∨ (False → p4)) → ((p3 ∨ True) → (True ∨ p5))))) := by
  apply Or.inr
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_2
    case inl assump_8 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        cases assump_1
        case inl assump_16 =>
          apply Or.inl
          apply True.intro
        case inr assump_17 =>
          apply Or.inl
          apply True.intro
    case inr assump_9 =>
      cases assump_1
      case inl assump_24 =>
        apply Or.inl
        apply True.intro
      case inr assump_25 =>
        apply Or.inl
        apply True.intro
  case inr assump_5 =>
    cases assump_2
    case inl assump_32 =>
      cases assump_32
      case intro assump_34 assump_35 =>
        cases assump_1
        case inl assump_40 =>
          apply Or.inl
          apply True.intro
        case inr assump_41 =>
          apply Or.inl
          apply True.intro
    case inr assump_33 =>
      cases assump_1
      case inl assump_48 =>
        apply Or.inl
        apply True.intro
      case inr assump_49 =>
        apply Or.inl
        apply True.intro


variable (p4 p0 p5 p1 p7 p6 : Prop)
theorem file26_33130 : (((((p7 → False) → (p0 ∨ p5)) ∨ ((p6 ∨ p5) → (p6 → False))) → (((False ∧ True) → (True ∧ False)) ∨ ((p6 → False) → False))) ∨ ((((p1 ∧ p5) ∨ (p7 → p1)) ∨ ((p6 → False) → (p4 → False))) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    apply And.intro
    apply True.intro
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_7
  case inr assump_3 =>
    apply Or.inl
    intro assump_13
    apply And.intro
    apply True.intro
    cases assump_13
    case intro assump_14 assump_15 =>
      apply False.elim assump_14


variable (p7 p3 p0 p1 p5 p2 p4 : Prop)
theorem file26_33822 : (((((True → False) ∧ (p0 → False)) → ((p2 ∧ True) ∨ (p3 ∧ p7))) ∨ (((p7 → False) → False) ∧ ((p3 ∧ p4) ∧ (p2 ∨ False)))) ∨ ((((False → True) ∧ (p1 → False)) → ((p0 → False) ∨ (False ∨ p5))) ∨ (((True → False) → (p3 → p5)) ∨ ((True → False) ∨ (False → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_13 : True := by
      apply True.intro
    let assump_9 := assump_2 assump_13
    apply False.elim assump_9


variable (p0 p7 p3 p6 p5 p4 : Prop)
theorem file26_34372 : (((((p7 → False) → False) → ((p5 ∧ p0) ∧ (False ∧ p7))) ∨ (((p7 ∨ False) ∨ (True ∧ False)) ∧ ((p6 ∧ p5) ∧ (p5 ∨ p4)))) → ((((True → False) → False) ∧ ((False ∧ p5) → (False → False))) ∨ (((p3 ∧ p6) ∧ (p3 → p5)) → False))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply And.intro
    intro assump_6
    have assump_69 : True := by
      apply True.intro
    let assump_9 := assump_6 assump_69
    apply False.elim assump_9
    intro assump_13
    intro assump_14
    apply False.elim assump_14
  case inr assump_3 =>
    cases assump_3
    case intro assump_17 assump_18 =>
      cases assump_17
      case inl assump_19 =>
        cases assump_19
        case inl assump_21 =>
          cases assump_18
          case intro assump_25 assump_26 =>
            cases assump_25
            case intro assump_27 assump_28 =>
              cases assump_26
              case inl assump_33 =>
                apply Or.inl
                apply And.intro
                intro assump_37
                have assump_70 : True := by
                  apply True.intro
                let assump_40 := assump_37 assump_70
                apply False.elim assump_40
                intro assump_44
                intro assump_45
                apply False.elim assump_45
              case inr assump_34 =>
                apply Or.inl
                apply And.intro
                intro assump_50
                have assump_71 : True := by
                  apply True.intro
                let assump_53 := assump_50 assump_71
                apply False.elim assump_53
                intro assump_57
                intro assump_58
                apply False.elim assump_58
        case inr assump_22 =>
          apply False.elim assump_22
      case inr assump_20 =>
        cases assump_20
        case intro assump_63 assump_64 =>
          apply False.elim assump_64


variable (p2 p7 p6 p5 p3 p1 p0 : Prop)
theorem file26_36349 : (((((p7 ∧ p0) → (p2 ∧ True)) → ((False ∨ True) ∨ (p6 → p1))) ∨ (((p5 ∨ p5) → (False ∧ p3)) ∧ ((False ∧ True) → False))) ∨ ((((p6 → p2) → (p5 ∨ p3)) → ((False ∧ p5) ∧ (p3 → False))) ∨ (((False ∨ False) ∧ (True → False)) → ((p0 → False) → (p7 ∧ p0))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_9
  apply Or.inl
  apply Or.inr
  apply True.intro


variable (p2 p3 p1 p4 p6 p5 p7 : Prop)
theorem file26_36765 : (((((p5 ∧ p7) → (p2 → p7)) ∨ ((p4 → p1) ∧ (p2 → False))) → (((p3 ∧ p3) ∨ (p2 → True)) → ((p4 ∨ p4) → False))) → ((((False ∧ True) ∧ (p2 ∨ p5)) → ((p5 → p2) → (p6 → False))) ∨ (((p4 → p5) → False) ∨ ((p2 ∧ p7) ∧ (p3 → False))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  intro assump_6
  cases assump_4
  case intro assump_11 assump_12 =>
    cases assump_11
    case intro assump_13 assump_14 =>
      apply False.elim assump_13


variable (p0 : Prop)
theorem file26_37271 : (((((p0 ∨ True) → False) → False) → False) → False) := by
  intro assump_1
  have assump_15 : (((p0 ∨ True) → False) → False) := by
    intro assump_5
    have assump_16 : (p0 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p4 p5 p1 p7 p2 p0 p6 : Prop)
theorem file26_37700 : (((((True ∨ p7) ∨ (p0 → p6)) ∨ ((p1 ∧ p5) → (p0 → False))) → False) → ((((p6 ∨ p4) ∨ (False → p4)) ∧ ((p2 → False) ∨ (False ∨ p2))) → (((p1 ∨ True) → False) → ((p7 ∧ p4) → False)))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_2
    case intro assump_13 assump_14 =>
      cases assump_13
      case inl assump_15 =>
        cases assump_15
        case inl assump_17 =>
          cases assump_14
          case inl assump_21 =>
            have assump_91 : (((True ∨ p7) ∨ (p0 → p6)) ∨ ((p1 ∧ p5) → (p0 → False))) := by
              apply Or.inl
              apply Or.inl
              apply Or.inl
              apply True.intro
            let assump_27 := assump_1 assump_91
            apply False.elim assump_27
          case inr assump_22 =>
            cases assump_22
            case inl assump_31 =>
              apply False.elim assump_31
            case inr assump_32 =>
              have assump_92 : (((True ∨ p7) ∨ (p0 → p6)) ∨ ((p1 ∧ p5) → (p0 → False))) := by
                apply Or.inl
                apply Or.inl
                apply Or.inl
                apply True.intro
              let assump_39 := assump_1 assump_92
              apply False.elim assump_39
        case inr assump_18 =>
          cases assump_14
          case inl assump_45 =>
            have assump_93 : (((True ∨ p7) ∨ (p0 → p6)) ∨ ((p1 ∧ p5) → (p0 → False))) := by
              apply Or.inl
              apply Or.inl
              apply Or.inl
              apply True.intro
            let assump_51 := assump_1 assump_93
            apply False.elim assump_51
          case inr assump_46 =>
            cases assump_46
            case inl assump_55 =>
              apply False.elim assump_55
            case inr assump_56 =>
              have assump_94 : (((True ∨ p7) ∨ (p0 → p6)) ∨ ((p1 ∧ p5) → (p0 → False))) := by
                apply Or.inl
                apply Or.inl
                apply Or.inl
                apply True.intro
              let assump_63 := assump_1 assump_94
              apply False.elim assump_63
      case inr assump_16 =>
        cases assump_14
        case inl assump_69 =>
          have assump_95 : (((True ∨ p7) ∨ (p0 → p6)) ∨ ((p1 ∧ p5) → (p0 → False))) := by
            apply Or.inl
            apply Or.inl
            apply Or.inl
            apply True.intro
          let assump_75 := assump_1 assump_95
          apply False.elim assump_75
        case inr assump_70 =>
          cases assump_70
          case inl assump_79 =>
            apply False.elim assump_79
          case inr assump_80 =>
            have assump_96 : (((True ∨ p7) ∨ (p0 → p6)) ∨ ((p1 ∧ p5) → (p0 → False))) := by
              apply Or.inl
              apply Or.inl
              apply Or.inl
              apply True.intro
            let assump_87 := assump_1 assump_96
            apply False.elim assump_87


variable (p7 p3 : Prop)
theorem file26_40701 : (((((p3 ∧ False) → False) ∨ ((p7 → p3) → (p7 ∨ True))) → False) → False) := by
  intro assump_20
  have assump_34 : (((p3 ∧ False) → False) ∨ ((p7 → p3) → (p7 ∨ True))) := by
    apply Or.inl
    intro assump_24
    cases assump_24
    case intro assump_25 assump_26 =>
      apply False.elim assump_26
  let assump_23 := assump_20 assump_34
  apply False.elim assump_23


variable (p6 p7 p4 p5 p2 p0 : Prop)
theorem file26_41132 : ((((((p4 ∨ p2) ∧ (p5 → p6)) → ((p5 ∨ True) ∨ (True → False))) ∧ (((p7 ∨ False) → False) → False)) ∧ ((((True ∨ p0) → False) → ((p4 → False) ∧ (p2 ∨ p0))) → False)) → False) := by
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    cases assump_10
    case intro assump_12 assump_13 =>
      have assump_40 : (((True ∨ p0) → False) → ((p4 → False) ∧ (p2 ∨ p0))) := by
        intro assump_21
        apply And.intro
        intro assump_22
        have assump_41 : (True ∨ p0) := by
          apply Or.inl
          apply True.intro
        let assump_27 := assump_21 assump_41
        apply False.elim assump_27
        have assump_42 : (True ∨ p0) := by
          apply Or.inl
          apply True.intro
        let assump_33 := assump_21 assump_42
        apply False.elim assump_33
      let assump_20 := assump_11 assump_40
      apply False.elim assump_20


variable (p6 p7 p0 p5 p4 p3 p1 : Prop)
theorem file26_42078 : ((((((p0 ∧ p4) → False) ∧ ((p6 → False) → (p4 → p5))) ∨ (((p4 ∨ p6) ∨ (p0 → p5)) ∧ ((p4 ∨ p1) ∧ (p0 ∧ p3)))) ∧ ((((p5 ∧ p3) ∧ (p3 → False)) ∧ ((False → True) → (p1 ∧ p5))) ∨ (((p3 ∨ p7) → False) ∧ ((p1 → True) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_3
        case inl assump_12 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              cases assump_16
              case intro assump_18 assump_19 =>
                have assump_336 : p3 := by
                  exact assump_19
                let assump_33 := assump_17 assump_336
                apply False.elim assump_33
        case inr assump_13 =>
          cases assump_13
          case intro assump_37 assump_38 =>
            have assump_337 : (p1 → True) := by
              intro assump_44
              apply True.intro
            let assump_43 := assump_38 assump_337
            apply False.elim assump_43
    case inr assump_5 =>
      cases assump_5
      case intro assump_48 assump_49 =>
        cases assump_48
        case inl assump_50 =>
          cases assump_50
          case inl assump_52 =>
            cases assump_49
            case intro assump_56 assump_57 =>
              cases assump_56
              case inl assump_58 =>
                cases assump_57
                case intro assump_62 assump_63 =>
                  cases assump_3
                  case inl assump_68 =>
                    cases assump_68
                    case intro assump_70 assump_71 =>
                      cases assump_70
                      case intro assump_72 assump_73 =>
                        cases assump_72
                        case intro assump_74 assump_75 =>
                          have assump_338 : p3 := by
                            exact assump_75
                          let assump_89 := assump_73 assump_338
                          apply False.elim assump_89
                  case inr assump_69 =>
                    cases assump_69
                    case intro assump_93 assump_94 =>
                      have assump_339 : (p1 → True) := by
                        intro assump_100
                        apply True.intro
                      let assump_99 := assump_94 assump_339
                      apply False.elim assump_99
              case inr assump_59 =>
                cases assump_57
                case intro assump_106 assump_107 =>
                  cases assump_3
                  case inl assump_112 =>
                    cases assump_112
                    case intro assump_114 assump_115 =>
                      cases assump_114
                      case intro assump_116 assump_117 =>
                        cases assump_116
                        case intro assump_118 assump_119 =>
                          have assump_340 : p3 := by
                            exact assump_119
                          let assump_133 := assump_117 assump_340
                          apply False.elim assump_133
                  case inr assump_113 =>
                    cases assump_113
                    case intro assump_137 assump_138 =>
                      have assump_341 : (p1 → True) := by
                        intro assump_144
                        apply True.intro
                      let assump_143 := assump_138 assump_341
                      apply False.elim assump_143
          case inr assump_53 =>
            cases assump_49
            case intro assump_150 assump_151 =>
              cases assump_150
              case inl assump_152 =>
                cases assump_151
                case intro assump_156 assump_157 =>
                  cases assump_3
                  case inl assump_162 =>
                    cases assump_162
                    case intro assump_164 assump_165 =>
                      cases assump_164
                      case intro assump_166 assump_167 =>
                        cases assump_166
                        case intro assump_168 assump_169 =>
                          have assump_342 : p3 := by
                            exact assump_169
                          let assump_183 := assump_167 assump_342
                          apply False.elim assump_183
                  case inr assump_163 =>
                    cases assump_163
                    case intro assump_187 assump_188 =>
                      have assump_343 : (p1 → True) := by
                        intro assump_194
                        apply True.intro
                      let assump_193 := assump_188 assump_343
                      apply False.elim assump_193
              case inr assump_153 =>
                cases assump_151
                case intro assump_200 assump_201 =>
                  cases assump_3
                  case inl assump_206 =>
                    cases assump_206
                    case intro assump_208 assump_209 =>
                      cases assump_208
                      case intro assump_210 assump_211 =>
                        cases assump_210
                        case intro assump_212 assump_213 =>
                          have assump_344 : p3 := by
                            exact assump_213
                          let assump_227 := assump_211 assump_344
                          apply False.elim assump_227
                  case inr assump_207 =>
                    cases assump_207
                    case intro assump_231 assump_232 =>
                      have assump_345 : (p1 → True) := by
                        intro assump_238
                        apply True.intro
                      let assump_237 := assump_232 assump_345
                      apply False.elim assump_237
        case inr assump_51 =>
          cases assump_49
          case intro assump_244 assump_245 =>
            cases assump_244
            case inl assump_246 =>
              cases assump_245
              case intro assump_250 assump_251 =>
                cases assump_3
                case inl assump_256 =>
                  cases assump_256
                  case intro assump_258 assump_259 =>
                    cases assump_258
                    case intro assump_260 assump_261 =>
                      cases assump_260
                      case intro assump_262 assump_263 =>
                        have assump_346 : p3 := by
                          exact assump_263
                        let assump_277 := assump_261 assump_346
                        apply False.elim assump_277
                case inr assump_257 =>
                  cases assump_257
                  case intro assump_281 assump_282 =>
                    have assump_347 : (p1 → True) := by
                      intro assump_288
                      apply True.intro
                    let assump_287 := assump_282 assump_347
                    apply False.elim assump_287
            case inr assump_247 =>
              cases assump_245
              case intro assump_294 assump_295 =>
                cases assump_3
                case inl assump_300 =>
                  cases assump_300
                  case intro assump_302 assump_303 =>
                    cases assump_302
                    case intro assump_304 assump_305 =>
                      cases assump_304
                      case intro assump_306 assump_307 =>
                        have assump_348 : p3 := by
                          exact assump_307
                        let assump_321 := assump_305 assump_348
                        apply False.elim assump_321
                case inr assump_301 =>
                  cases assump_301
                  case intro assump_325 assump_326 =>
                    have assump_349 : (p1 → True) := by
                      intro assump_332
                      apply True.intro
                    let assump_331 := assump_326 assump_349
                    apply False.elim assump_331


variable (p5 p4 p1 p7 p0 : Prop)
theorem file26_50289 : ((((((False → False) → (p7 → False)) ∨ ((True ∧ False) ∨ (False ∨ p4))) ∨ (((p1 → False) ∨ (p7 → True)) ∧ ((p0 → False) ∨ (False ∧ p4)))) ∧ ((((p5 ∨ p7) ∧ (False → False)) → False) ∧ (((True → False) → (p0 → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_3
        case intro assump_10 assump_11 =>
          have assump_128 : ((True → False) → (p0 → False)) := by
            intro assump_17
            intro assump_18
            have assump_129 : True := by
              apply True.intro
            let assump_23 := assump_17 assump_129
            apply False.elim assump_23
          let assump_16 := assump_11 assump_128
          apply False.elim assump_16
      case inr assump_7 =>
        cases assump_7
        case inl assump_30 =>
          cases assump_30
          case intro assump_32 assump_33 =>
            apply False.elim assump_33
        case inr assump_31 =>
          cases assump_31
          case inl assump_38 =>
            apply False.elim assump_38
          case inr assump_39 =>
            cases assump_3
            case intro assump_44 assump_45 =>
              have assump_130 : ((True → False) → (p0 → False)) := by
                intro assump_51
                intro assump_52
                have assump_131 : True := by
                  apply True.intro
                let assump_57 := assump_51 assump_131
                apply False.elim assump_57
              let assump_50 := assump_45 assump_130
              apply False.elim assump_50
    case inr assump_5 =>
      cases assump_5
      case intro assump_64 assump_65 =>
        cases assump_64
        case inl assump_66 =>
          cases assump_65
          case inl assump_70 =>
            cases assump_3
            case intro assump_74 assump_75 =>
              have assump_132 : ((True → False) → (p0 → False)) := by
                intro assump_81
                intro assump_82
                have assump_133 : True := by
                  apply True.intro
                let assump_87 := assump_81 assump_133
                apply False.elim assump_87
              let assump_80 := assump_75 assump_132
              apply False.elim assump_80
          case inr assump_71 =>
            cases assump_71
            case intro assump_94 assump_95 =>
              apply False.elim assump_94
        case inr assump_67 =>
          cases assump_65
          case inl assump_100 =>
            cases assump_3
            case intro assump_104 assump_105 =>
              have assump_134 : ((True → False) → (p0 → False)) := by
                intro assump_111
                intro assump_112
                have assump_135 : True := by
                  apply True.intro
                let assump_117 := assump_111 assump_135
                apply False.elim assump_117
              let assump_110 := assump_105 assump_134
              apply False.elim assump_110
          case inr assump_101 =>
            cases assump_101
            case intro assump_124 assump_125 =>
              apply False.elim assump_124


variable (p6 p3 p1 : Prop)
theorem file26_53550 : (((((p6 ∧ False) → False) ∨ ((p3 → p3) → (p6 → False))) → False) → ((((p1 → False) → False) → False) → False)) := by
  intro assump_1
  intro assump_2
  have assump_18 : (((p6 ∧ False) → False) ∨ ((p3 → p3) → (p6 → False))) := by
    apply Or.inl
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      apply False.elim assump_10
  let assump_7 := assump_1 assump_18
  apply False.elim assump_7


variable (p0 p7 p1 p2 p4 p3 p6 p5 : Prop)
theorem file26_54036 : (((((p4 ∨ p3) → (p5 ∧ p7)) → ((p2 ∨ p5) → False)) → (((p6 ∧ p5) ∨ (p5 ∧ p4)) → ((p4 ∧ p4) → (p4 → p5)))) ∨ ((((p5 → True) ∨ (p3 → p3)) → False) ∨ (((p1 ∨ p5) ∨ (p5 → p5)) → ((p2 → p0) → (p0 ∨ p6))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_3
  case intro assump_7 assump_8 =>
    cases assump_2
    case inl assump_13 =>
      cases assump_13
      case intro assump_15 assump_16 =>
        exact assump_16
    case inr assump_14 =>
      cases assump_14
      case intro assump_23 assump_24 =>
        exact assump_23


variable (p0 p7 p3 p6 p4 : Prop)
theorem file26_54676 : (((((True → p4) → (True ∧ p7)) → ((False → p6) ∨ (p3 ∨ p0))) → False) → False) := by
  intro assump_1
  have assump_14 : (((True → p4) → (True ∧ p7)) → ((False → p6) ∨ (p3 ∨ p0))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p7 p3 p5 p2 p0 : Prop)
theorem file26_55069 : ((((((p7 → p5) → (p0 → p7)) ∧ ((p0 ∧ True) → False)) → (((p0 ∧ True) ∨ (p3 ∨ True)) → ((p2 → p0) → (p7 → p7)))) → False) → False) := by
  intro assump_20
  have assump_67 : ((((p7 → p5) → (p0 → p7)) ∧ ((p0 ∧ True) → False)) → (((p0 ∧ True) ∨ (p3 ∨ True)) → ((p2 → p0) → (p7 → p7)))) := by
    intro assump_24
    intro assump_25
    intro assump_26
    intro assump_27
    cases assump_25
    case inl assump_32 =>
      cases assump_32
      case intro assump_34 assump_35 =>
        cases assump_24
        case intro assump_40 assump_41 =>
          exact assump_27
    case inr assump_33 =>
      cases assump_33
      case inl assump_46 =>
        cases assump_24
        case intro assump_50 assump_51 =>
          exact assump_27
      case inr assump_47 =>
        cases assump_24
        case intro assump_58 assump_59 =>
          exact assump_27
  let assump_23 := assump_20 assump_67
  apply False.elim assump_23


variable (p7 p5 p3 p1 p4 : Prop)
theorem file26_56051 : (((((p3 → False) → False) ∧ ((p1 ∨ p5) → False)) ∧ (((p4 → False) ∧ (p7 → False)) ∧ ((p5 ∨ False) ∨ (p3 ∧ p5)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_11
          case inl assump_18 =>
            cases assump_18
            case inl assump_20 =>
              have assump_47 : (p1 ∨ p5) := by
                apply Or.inr
                exact assump_20
              let assump_27 := assump_5 assump_47
              apply False.elim assump_27
            case inr assump_21 =>
              apply False.elim assump_21
          case inr assump_19 =>
            cases assump_19
            case intro assump_33 assump_34 =>
              have assump_48 : (p1 ∨ p5) := by
                apply Or.inr
                exact assump_34
              let assump_43 := assump_5 assump_48
              apply False.elim assump_43


variable (p4 p5 p3 p7 p0 p6 p2 p1 : Prop)
theorem file26_57194 : ((((((False ∧ p5) ∨ (p1 → p4)) → ((p0 ∧ p0) → (p2 ∨ p6))) ∨ (((True ∧ True) ∨ (p3 ∧ p7)) → False)) ∧ ((((p2 ∧ p1) → (p2 ∨ p3)) → False) ∧ (((p2 ∧ p0) ∧ (p5 → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        have assump_46 : ((p2 ∧ p1) → (p2 ∨ p3)) := by
          intro assump_16
          cases assump_16
          case intro assump_17 assump_18 =>
            apply Or.inl
            exact assump_17
        let assump_15 := assump_8 assump_46
        apply False.elim assump_15
    case inr assump_5 =>
      cases assump_3
      case intro assump_28 assump_29 =>
        have assump_47 : ((p2 ∧ p1) → (p2 ∨ p3)) := by
          intro assump_36
          cases assump_36
          case intro assump_37 assump_38 =>
            apply Or.inl
            exact assump_37
        let assump_35 := assump_28 assump_47
        apply False.elim assump_35


variable (p6 p3 p0 p1 p7 p2 : Prop)
theorem file26_58270 : ((((((p0 ∧ p1) ∧ (p7 ∨ p6)) → ((True ∧ True) ∨ (p2 → False))) ∨ (((p2 → p3) → (True ∨ True)) ∨ ((p6 ∧ p3) → False))) → False) → False) := by
  intro assump_1
  have assump_23 : ((((p0 ∧ p1) ∧ (p7 ∨ p6)) → ((True ∧ True) ∨ (p2 → False))) ∨ (((p2 → p3) → (True ∨ True)) ∨ ((p6 ∧ p3) → False))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case inl assump_14 =>
          apply Or.inl
          apply And.intro
          apply True.intro
          apply True.intro
        case inr assump_15 =>
          apply Or.inl
          apply And.intro
          apply True.intro
          apply True.intro
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p3 p0 p1 p4 p6 : Prop)
theorem file26_59129 : (((((True ∧ p3) ∧ (False → False)) → False) → (((p0 → p6) → False) → ((p1 ∧ p6) → False))) ∨ ((((p1 ∧ p1) → False) ∨ ((p4 → False) → False)) → (((p3 → False) → False) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    have assump_22 : (p0 → p6) := by
      intro assump_16
      exact assump_5
    let assump_15 := assump_2 assump_22
    apply False.elim assump_15


variable (p4 p6 p1 p5 p0 p2 p7 : Prop)
theorem file26_59644 : (((((p0 → False) ∨ (True → False)) ∧ ((p5 → False) ∨ (p0 → p4))) ∨ (((False → False) ∧ (p6 ∨ p4)) → False)) → ((((p4 ∧ p2) ∧ (True → False)) ∧ ((p1 → p1) → (True ∨ p5))) → (((True → False) → (p1 ∧ p1)) ∨ ((p6 → p0) ∧ (p7 → False))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        cases assump_1
        case inl assump_17 =>
          cases assump_17
          case intro assump_19 assump_20 =>
            cases assump_19
            case inl assump_21 =>
              cases assump_20
              case inl assump_25 =>
                apply Or.inl
                intro assump_29
                apply And.intro
                have assump_106 : True := by
                  apply True.intro
                let assump_32 := assump_29 assump_106
                apply False.elim assump_32
                have assump_107 : True := by
                  apply True.intro
                let assump_38 := assump_29 assump_107
                apply False.elim assump_38
              case inr assump_26 =>
                apply Or.inl
                intro assump_44
                apply And.intro
                have assump_108 : True := by
                  apply True.intro
                let assump_47 := assump_44 assump_108
                apply False.elim assump_47
                have assump_109 : True := by
                  apply True.intro
                let assump_53 := assump_44 assump_109
                apply False.elim assump_53
            case inr assump_22 =>
              cases assump_20
              case inl assump_59 =>
                apply Or.inl
                intro assump_63
                apply And.intro
                have assump_110 : True := by
                  apply True.intro
                let assump_66 := assump_63 assump_110
                apply False.elim assump_66
                have assump_111 : True := by
                  apply True.intro
                let assump_72 := assump_63 assump_111
                apply False.elim assump_72
              case inr assump_60 =>
                apply Or.inl
                intro assump_78
                apply And.intro
                have assump_112 : True := by
                  apply True.intro
                let assump_81 := assump_78 assump_112
                apply False.elim assump_81
                have assump_113 : True := by
                  apply True.intro
                let assump_87 := assump_78 assump_113
                apply False.elim assump_87
        case inr assump_18 =>
          apply Or.inl
          intro assump_93
          apply And.intro
          have assump_114 : True := by
            apply True.intro
          let assump_96 := assump_93 assump_114
          apply False.elim assump_96
          have assump_115 : True := by
            apply True.intro
          let assump_102 := assump_93 assump_115
          apply False.elim assump_102


variable (p3 p4 p5 : Prop)
theorem file26_62758 : ((((((p5 ∨ p4) → False) ∧ ((False ∧ p3) ∨ (True → False))) → False) → False) → False) := by
  intro assump_14
  have assump_38 : ((((p5 ∨ p4) → False) ∧ ((False ∧ p3) ∨ (True → False))) → False) := by
    intro assump_18
    cases assump_18
    case intro assump_19 assump_20 =>
      cases assump_20
      case inl assump_23 =>
        cases assump_23
        case intro assump_25 assump_26 =>
          apply False.elim assump_25
      case inr assump_24 =>
        have assump_39 : True := by
          apply True.intro
        let assump_31 := assump_24 assump_39
        apply False.elim assump_31
  let assump_17 := assump_14 assump_38
  apply False.elim assump_17


variable (p2 p7 p4 p3 p5 p1 : Prop)
theorem file26_63489 : (((((True → True) ∨ (p5 ∨ p4)) ∧ ((p5 ∨ p4) ∧ (p5 → True))) ∧ (((p1 → p7) → False) → False)) → ((((p1 → True) → False) → False) ∨ (((p2 ∧ True) → False) → ((p3 ∧ False) ∨ (True ∧ p5))))) := by
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
            apply Or.inl
            intro assump_20
            have assump_112 : (p1 → True) := by
              intro assump_24
              apply True.intro
            let assump_23 := assump_20 assump_112
            apply False.elim assump_23
          case inr assump_13 =>
            apply Or.inl
            intro assump_34
            have assump_113 : (p1 → True) := by
              intro assump_38
              apply True.intro
            let assump_37 := assump_34 assump_113
            apply False.elim assump_37
      case inr assump_7 =>
        cases assump_7
        case inl assump_42 =>
          cases assump_5
          case intro assump_46 assump_47 =>
            cases assump_46
            case inl assump_48 =>
              apply Or.inl
              intro assump_56
              have assump_114 : (p1 → True) := by
                intro assump_60
                apply True.intro
              let assump_59 := assump_56 assump_114
              apply False.elim assump_59
            case inr assump_49 =>
              apply Or.inl
              intro assump_70
              have assump_115 : (p1 → True) := by
                intro assump_74
                apply True.intro
              let assump_73 := assump_70 assump_115
              apply False.elim assump_73
        case inr assump_43 =>
          cases assump_5
          case intro assump_80 assump_81 =>
            cases assump_80
            case inl assump_82 =>
              apply Or.inl
              intro assump_90
              have assump_116 : (p1 → True) := by
                intro assump_94
                apply True.intro
              let assump_93 := assump_90 assump_116
              apply False.elim assump_93
            case inr assump_83 =>
              apply Or.inl
              intro assump_104
              have assump_117 : (p1 → True) := by
                intro assump_108
                apply True.intro
              let assump_107 := assump_104 assump_117
              apply False.elim assump_107


variable (p5 p3 : Prop)
theorem file26_66063 : ((((((p5 ∧ False) → (p3 → False)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_25 : ((((p5 ∧ False) → (p3 → False)) → False) → False) := by
    intro assump_5
    have assump_26 : ((p5 ∧ False) → (p3 → False)) := by
      intro assump_9
      intro assump_10
      cases assump_9
      case intro assump_13 assump_14 =>
        apply False.elim assump_14
    let assump_8 := assump_5 assump_26
    apply False.elim assump_8
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p5 p0 p2 p3 p4 p1 p7 p6 : Prop)
theorem file26_66646 : (((((True → True) → False) ∧ ((p4 → False) ∧ (p1 ∧ p2))) ∧ (((False → p7) ∨ (True → False)) ∨ ((p6 ∧ p6) ∨ (p5 ∧ p1)))) → ((((p2 ∧ p3) → False) → False) → (((p7 ∨ True) → False) → ((p0 ∨ p5) ∧ (p4 ∨ False))))) := by
  intro assump_26
  intro assump_27
  intro assump_28
  apply And.intro
  cases assump_26
  case intro assump_33 assump_34 =>
    cases assump_33
    case intro assump_35 assump_36 =>
      cases assump_36
      case intro assump_39 assump_40 =>
        cases assump_40
        case intro assump_43 assump_44 =>
          cases assump_34
          case inl assump_49 =>
            cases assump_49
            case inl assump_51 =>
              have assump_169 : (True → True) := by
                intro assump_60
                apply True.intro
              let assump_59 := assump_35 assump_169
              apply False.elim assump_59
            case inr assump_52 =>
              have assump_170 : True := by
                apply True.intro
              let assump_66 := assump_52 assump_170
              apply False.elim assump_66
          case inr assump_50 =>
            cases assump_50
            case inl assump_70 =>
              cases assump_70
              case intro assump_72 assump_73 =>
                have assump_171 : (True → True) := by
                  intro assump_84
                  apply True.intro
                let assump_83 := assump_35 assump_171
                apply False.elim assump_83
            case inr assump_71 =>
              cases assump_71
              case intro assump_88 assump_89 =>
                apply Or.inr
                exact assump_88
  cases assump_26
  case intro assump_98 assump_99 =>
    cases assump_98
    case intro assump_100 assump_101 =>
      cases assump_101
      case intro assump_104 assump_105 =>
        cases assump_105
        case intro assump_108 assump_109 =>
          cases assump_99
          case inl assump_114 =>
            cases assump_114
            case inl assump_116 =>
              have assump_172 : (True → True) := by
                intro assump_125
                apply True.intro
              let assump_124 := assump_100 assump_172
              apply False.elim assump_124
            case inr assump_117 =>
              have assump_173 : True := by
                apply True.intro
              let assump_131 := assump_117 assump_173
              apply False.elim assump_131
          case inr assump_115 =>
            cases assump_115
            case inl assump_135 =>
              cases assump_135
              case intro assump_137 assump_138 =>
                have assump_174 : (True → True) := by
                  intro assump_149
                  apply True.intro
                let assump_148 := assump_100 assump_174
                apply False.elim assump_148
            case inr assump_136 =>
              cases assump_136
              case intro assump_153 assump_154 =>
                have assump_175 : (True → True) := by
                  intro assump_165
                  apply True.intro
                let assump_164 := assump_100 assump_175
                apply False.elim assump_164


variable (p3 p6 p5 p7 p4 p2 p1 : Prop)
theorem file26_69869 : (((((p6 ∨ True) ∨ (p3 ∨ p7)) ∨ ((p4 → p5) ∧ (True ∧ p5))) → (((False ∧ False) ∨ (p5 → p7)) → ((p3 ∧ p3) → (True ∨ p1)))) ∨ ((((p2 → p7) → (p2 ∧ p4)) → ((p3 ∧ p2) → (False → False))) ∧ (((p2 → p5) → False) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_2
    case inl assump_10 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        apply False.elim assump_12
    case inr assump_11 =>
      cases assump_1
      case inl assump_18 =>
        cases assump_18
        case inl assump_20 =>
          cases assump_20
          case inl assump_22 =>
            apply Or.inl
            apply True.intro
          case inr assump_23 =>
            apply Or.inl
            apply True.intro
        case inr assump_21 =>
          cases assump_21
          case inl assump_28 =>
            apply Or.inl
            apply True.intro
          case inr assump_29 =>
            apply Or.inl
            apply True.intro
      case inr assump_19 =>
        cases assump_19
        case intro assump_34 assump_35 =>
          cases assump_35
          case intro assump_38 assump_39 =>
            apply Or.inl
            apply True.intro


variable (p4 p2 p6 p1 p3 p7 p0 p5 : Prop)
theorem file26_71189 : ((((((p7 → False) → (p0 → False)) ∨ ((p7 → p6) → (p5 → False))) → (((p0 → p3) → (p0 → True)) ∨ ((p4 → p7) ∧ (p3 ∧ p1)))) → ((((p4 → True) → False) → ((p2 ∨ p6) ∧ (p4 ∨ True))) → False)) → False) := by
  intro assump_1
  have assump_30 : ((((p7 → False) → (p0 → False)) ∨ ((p7 → p6) → (p5 → False))) → (((p0 → p3) → (p0 → True)) ∨ ((p4 → p7) ∧ (p3 ∧ p1)))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inl
      intro assump_10
      intro assump_11
      apply True.intro
    case inr assump_7 =>
      apply Or.inl
      intro assump_14
      intro assump_15
      apply True.intro
  let assump_4 := assump_1 assump_30
  have assump_31 : (((p4 → True) → False) → ((p2 ∨ p6) ∧ (p4 ∨ True))) := by
    intro assump_17
    apply And.intro
    have assump_32 : (p4 → True) := by
      intro assump_21
      apply True.intro
    let assump_20 := assump_17 assump_32
    apply False.elim assump_20
    apply Or.inr
    apply True.intro
  let assump_16 := assump_4 assump_31
  apply False.elim assump_16


variable (p0 p4 p1 p2 p7 : Prop)
theorem file26_72283 : (((((False ∨ p0) → (False → False)) → False) ∧ (((p2 → True) ∨ (p4 → False)) → False)) → ((((p1 ∨ p4) ∨ (p2 ∨ p7)) → False) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    have assump_16 : ((p2 → True) ∨ (p4 → False)) := by
      apply Or.inl
      intro assump_12
      apply True.intro
    let assump_11 := assump_6 assump_16
    apply False.elim assump_11


variable (p1 p7 p4 p3 p0 p2 p5 : Prop)
theorem file26_72762 : (((((p5 → False) ∧ (p3 ∨ True)) ∨ ((p5 ∨ p3) → False)) → (((p5 → False) → (False → False)) ∨ ((False ∧ True) ∨ (p4 → p2)))) ∨ ((((p1 ∨ p4) ∧ (p7 → False)) ∨ ((p5 → p4) ∨ (p0 ∨ p2))) → (((p0 → p1) → False) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        apply Or.inl
        intro assump_12
        intro assump_13
        apply False.elim assump_13
      case inr assump_9 =>
        apply Or.inl
        intro assump_18
        intro assump_19
        apply False.elim assump_19
  case inr assump_3 =>
    apply Or.inl
    intro assump_24
    intro assump_25
    apply False.elim assump_25


variable (p0 p2 p6 p4 p7 p3 p5 : Prop)
theorem file26_73568 : (((((False → False) → (False ∧ p2)) ∧ ((p4 ∧ p5) → False)) ∧ (((p7 → False) ∧ (True → p6)) → False)) → ((((p0 ∨ False) ∨ (True ∧ False)) → ((p0 ∧ False) → (p7 → False))) ∨ (((p3 → p2) ∧ (p0 ∨ False)) → ((p0 → p7) → (p4 → p4))))) := by
  intro assump_12
  cases assump_12
  case intro assump_13 assump_14 =>
    cases assump_13
    case intro assump_15 assump_16 =>
      apply Or.inl
      intro assump_23
      intro assump_24
      intro assump_25
      cases assump_24
      case intro assump_28 assump_29 =>
        apply False.elim assump_29


variable (p0 p7 p3 p6 p5 p4 p1 p2 : Prop)
theorem file26_74181 : (((((p2 → False) → False) → False) ∧ (((p4 ∨ p7) → (p5 → p5)) ∨ ((p1 → False) → False))) → ((((p1 ∧ p2) ∧ (p1 ∨ p7)) → ((p0 ∨ p2) ∨ (p0 → p7))) ∨ (((p3 → p0) ∧ (p6 → False)) ∨ ((True ∧ p7) → (p1 ∨ p4))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      apply Or.inl
      intro assump_10
      cases assump_10
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          cases assump_12
          case inl assump_19 =>
            apply Or.inl
            apply Or.inr
            exact assump_14
          case inr assump_20 =>
            apply Or.inl
            apply Or.inr
            exact assump_14
    case inr assump_7 =>
      apply Or.inl
      intro assump_27
      cases assump_27
      case intro assump_28 assump_29 =>
        cases assump_28
        case intro assump_30 assump_31 =>
          cases assump_29
          case inl assump_36 =>
            apply Or.inl
            apply Or.inr
            exact assump_31
          case inr assump_37 =>
            apply Or.inl
            apply Or.inr
            exact assump_31


variable (p2 p4 p6 p5 p7 p3 p0 p1 : Prop)
theorem file26_75425 : (((((p4 → p4) → (p6 ∨ p0)) → False) → (((p1 → False) → (False → p5)) ∧ ((p7 → True) ∨ (p6 ∨ False)))) ∨ ((((True → False) ∧ (p5 ∧ p2)) → False) ∨ (((p1 → False) → (p3 → p1)) ∨ ((p7 ∧ p3) → (p6 → False))))) := by
  apply Or.inl
  intro assump_19
  apply And.intro
  intro assump_20
  intro assump_21
  apply False.elim assump_21
  apply Or.inl
  intro assump_26
  apply True.intro


variable (p3 p6 p0 p2 p7 p4 p1 : Prop)
theorem file26_75868 : ((((((p1 → False) ∧ (p2 ∨ p0)) → ((p0 ∧ p0) → False)) → False) ∧ ((((p0 ∧ p6) ∨ (p4 ∧ p0)) ∧ ((p0 ∨ p7) → False)) ∧ (((p3 ∧ True) ∧ (p7 ∧ p7)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            have assump_42 : (p0 ∨ p7) := by
              apply Or.inl
              exact assump_12
            let assump_23 := assump_9 assump_42
            apply False.elim assump_23
        case inr assump_11 =>
          cases assump_11
          case intro assump_27 assump_28 =>
            have assump_43 : (p0 ∨ p7) := by
              apply Or.inl
              exact assump_28
            let assump_38 := assump_9 assump_43
            apply False.elim assump_38


variable (p4 p5 p1 p0 p7 p3 p6 : Prop)
theorem file26_76883 : (((((p0 → p0) → False) → False) → (((False ∧ True) ∧ (p5 → p3)) → False)) ∨ ((((p0 ∨ p3) ∧ (p7 ∨ p6)) ∨ ((p6 ∨ p1) ∧ (p1 ∨ p0))) → (((p4 ∧ p1) → (False ∧ p6)) ∨ ((True → True) → False)))) := by
  apply Or.inl
  intro assump_25
  intro assump_26
  cases assump_26
  case intro assump_27 assump_28 =>
    cases assump_27
    case intro assump_29 assump_30 =>
      apply False.elim assump_29


variable (p6 p0 p1 p2 p3 p7 p4 : Prop)
theorem file26_77336 : (((((p1 → p3) ∧ (p2 → False)) ∧ ((p6 → False) → False)) ∨ (((p2 ∧ p1) ∨ (p1 → False)) → False)) → ((((True ∨ p0) ∧ (p4 ∧ p3)) ∨ ((False ∧ p6) → False)) ∨ (((True → p4) ∧ (p3 ∨ p3)) → ((p1 → p4) ∨ (p7 ∧ p6))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        apply Or.inl
        apply Or.inr
        intro assump_14
        cases assump_14
        case intro assump_15 assump_16 =>
          apply False.elim assump_15
  case inr assump_3 =>
    apply Or.inl
    apply Or.inr
    intro assump_21
    cases assump_21
    case intro assump_22 assump_23 =>
      apply False.elim assump_22


variable (p1 p6 p5 p7 p2 p4 : Prop)
theorem file26_78120 : (((((True → False) ∧ (True ∧ p5)) → False) ∨ (((p2 → False) ∧ (p4 → False)) ∨ ((p1 ∨ p6) → False))) ∨ ((((p4 ∧ p2) ∨ (p7 → False)) ∨ ((p7 ∧ p2) → False)) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_17 : True := by
        apply True.intro
      let assump_13 := assump_2 assump_17
      apply False.elim assump_13


variable (p1 p4 p7 p6 p2 : Prop)
theorem file26_78634 : (((((False ∧ p2) ∧ (p1 ∧ p7)) ∧ ((False → p4) ∧ (p7 ∨ p6))) ∧ (((p1 → True) → False) ∧ ((p6 → False) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          apply False.elim assump_8


variable (p4 p5 p1 p0 : Prop)
theorem file26_79096 : (((((p4 → False) ∨ (p5 ∨ p0)) → False) ∧ (((p1 → p1) → False) ∧ ((p1 → p0) ∨ (True ∨ p1)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        have assump_43 : (p1 → p1) := by
          intro assump_16
          exact assump_16
        let assump_15 := assump_6 assump_43
        apply False.elim assump_15
      case inr assump_11 =>
        cases assump_11
        case inl assump_22 =>
          have assump_44 : (p1 → p1) := by
            intro assump_27
            exact assump_27
          let assump_26 := assump_6 assump_44
          apply False.elim assump_26
        case inr assump_23 =>
          have assump_45 : (p1 → p1) := by
            intro assump_37
            exact assump_37
          let assump_36 := assump_6 assump_45
          apply False.elim assump_36


variable (p4 p5 p6 p2 p1 : Prop)
theorem file26_80080 : ((((((p2 → False) → False) ∧ ((p1 ∧ True) → (p6 ∧ p5))) → False) ∧ ((((False → False) → (False ∨ p5)) → ((False ∨ p6) → (False → p4))) ∧ (((False → False) → (p2 → p2)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_22 : ((False → False) → (p2 → p2)) := by
        intro assump_13
        intro assump_14
        exact assump_14
      let assump_12 := assump_7 assump_22
      apply False.elim assump_12


variable (p1 p5 p4 p6 p0 p3 p7 p2 : Prop)
theorem file26_80669 : (((((False → False) ∧ (True ∨ p5)) → False) ∧ (((p0 → p3) ∨ (p2 ∨ False)) ∧ ((p3 → False) ∨ (p7 ∨ False)))) → ((((p6 → False) ∧ (p2 → False)) ∧ ((p1 ∧ p0) ∨ (p3 → p6))) ∧ (((p6 → False) → False) ∧ ((p7 ∧ p4) → (p4 → False))))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        cases assump_10
        case inl assump_15 =>
          have assump_387 : ((False → False) ∧ (True ∨ p5)) := by
            apply And.intro
            intro assump_22
            apply False.elim assump_22
            apply Or.inl
            apply True.intro
          let assump_21 := assump_5 assump_387
          apply False.elim assump_21
        case inr assump_16 =>
          cases assump_16
          case inl assump_28 =>
            have assump_388 : ((False → False) ∧ (True ∨ p5)) := by
              apply And.intro
              intro assump_35
              apply False.elim assump_35
              apply Or.inl
              apply True.intro
            let assump_34 := assump_5 assump_388
            apply False.elim assump_34
          case inr assump_29 =>
            apply False.elim assump_29
      case inr assump_12 =>
        cases assump_12
        case inl assump_43 =>
          cases assump_10
          case inl assump_47 =>
            have assump_389 : ((False → False) ∧ (True ∨ p5)) := by
              apply And.intro
              intro assump_54
              apply False.elim assump_54
              apply Or.inl
              apply True.intro
            let assump_53 := assump_5 assump_389
            apply False.elim assump_53
          case inr assump_48 =>
            cases assump_48
            case inl assump_60 =>
              have assump_390 : ((False → False) ∧ (True ∨ p5)) := by
                apply And.intro
                intro assump_67
                apply False.elim assump_67
                apply Or.inl
                apply True.intro
              let assump_66 := assump_5 assump_390
              apply False.elim assump_66
            case inr assump_61 =>
              apply False.elim assump_61
        case inr assump_44 =>
          apply False.elim assump_44
  intro assump_77
  cases assump_1
  case intro assump_80 assump_81 =>
    cases assump_81
    case intro assump_84 assump_85 =>
      cases assump_84
      case inl assump_86 =>
        cases assump_85
        case inl assump_90 =>
          have assump_391 : ((False → False) ∧ (True ∨ p5)) := by
            apply And.intro
            intro assump_97
            apply False.elim assump_97
            apply Or.inl
            apply True.intro
          let assump_96 := assump_80 assump_391
          apply False.elim assump_96
        case inr assump_91 =>
          cases assump_91
          case inl assump_103 =>
            have assump_392 : ((False → False) ∧ (True ∨ p5)) := by
              apply And.intro
              intro assump_110
              apply False.elim assump_110
              apply Or.inl
              apply True.intro
            let assump_109 := assump_80 assump_392
            apply False.elim assump_109
          case inr assump_104 =>
            apply False.elim assump_104
      case inr assump_87 =>
        cases assump_87
        case inl assump_118 =>
          cases assump_85
          case inl assump_122 =>
            have assump_393 : ((False → False) ∧ (True ∨ p5)) := by
              apply And.intro
              intro assump_129
              apply False.elim assump_129
              apply Or.inl
              apply True.intro
            let assump_128 := assump_80 assump_393
            apply False.elim assump_128
          case inr assump_123 =>
            cases assump_123
            case inl assump_135 =>
              have assump_394 : ((False → False) ∧ (True ∨ p5)) := by
                apply And.intro
                intro assump_142
                apply False.elim assump_142
                apply Or.inl
                apply True.intro
              let assump_141 := assump_80 assump_394
              apply False.elim assump_141
            case inr assump_136 =>
              apply False.elim assump_136
        case inr assump_119 =>
          apply False.elim assump_119
  cases assump_1
  case intro assump_152 assump_153 =>
    cases assump_153
    case intro assump_156 assump_157 =>
      cases assump_156
      case inl assump_158 =>
        cases assump_157
        case inl assump_162 =>
          apply Or.inr
          intro assump_166
          have assump_395 : p3 := by
            exact assump_166
          let assump_170 := assump_162 assump_395
          apply False.elim assump_170
        case inr assump_163 =>
          cases assump_163
          case inl assump_174 =>
            apply Or.inr
            intro assump_178
            have assump_396 : ((False → False) ∧ (True ∨ p5)) := by
              apply And.intro
              intro assump_185
              apply False.elim assump_185
              apply Or.inl
              apply True.intro
            let assump_184 := assump_152 assump_396
            apply False.elim assump_184
          case inr assump_175 =>
            apply False.elim assump_175
      case inr assump_159 =>
        cases assump_159
        case inl assump_193 =>
          cases assump_157
          case inl assump_197 =>
            apply Or.inr
            intro assump_201
            have assump_397 : p3 := by
              exact assump_201
            let assump_205 := assump_197 assump_397
            apply False.elim assump_205
          case inr assump_198 =>
            cases assump_198
            case inl assump_209 =>
              apply Or.inr
              intro assump_213
              have assump_398 : ((False → False) ∧ (True ∨ p5)) := by
                apply And.intro
                intro assump_220
                apply False.elim assump_220
                apply Or.inl
                apply True.intro
              let assump_219 := assump_152 assump_398
              apply False.elim assump_219
            case inr assump_210 =>
              apply False.elim assump_210
        case inr assump_194 =>
          apply False.elim assump_194
  apply And.intro
  intro assump_230
  cases assump_1
  case intro assump_233 assump_234 =>
    cases assump_234
    case intro assump_237 assump_238 =>
      cases assump_237
      case inl assump_239 =>
        cases assump_238
        case inl assump_243 =>
          have assump_399 : ((False → False) ∧ (True ∨ p5)) := by
            apply And.intro
            intro assump_250
            apply False.elim assump_250
            apply Or.inl
            apply True.intro
          let assump_249 := assump_233 assump_399
          apply False.elim assump_249
        case inr assump_244 =>
          cases assump_244
          case inl assump_256 =>
            have assump_400 : ((False → False) ∧ (True ∨ p5)) := by
              apply And.intro
              intro assump_263
              apply False.elim assump_263
              apply Or.inl
              apply True.intro
            let assump_262 := assump_233 assump_400
            apply False.elim assump_262
          case inr assump_257 =>
            apply False.elim assump_257
      case inr assump_240 =>
        cases assump_240
        case inl assump_271 =>
          cases assump_238
          case inl assump_275 =>
            have assump_401 : ((False → False) ∧ (True ∨ p5)) := by
              apply And.intro
              intro assump_282
              apply False.elim assump_282
              apply Or.inl
              apply True.intro
            let assump_281 := assump_233 assump_401
            apply False.elim assump_281
          case inr assump_276 =>
            cases assump_276
            case inl assump_288 =>
              have assump_402 : ((False → False) ∧ (True ∨ p5)) := by
                apply And.intro
                intro assump_295
                apply False.elim assump_295
                apply Or.inl
                apply True.intro
              let assump_294 := assump_233 assump_402
              apply False.elim assump_294
            case inr assump_289 =>
              apply False.elim assump_289
        case inr assump_272 =>
          apply False.elim assump_272
  intro assump_305
  intro assump_306
  cases assump_305
  case intro assump_309 assump_310 =>
    cases assump_1
    case intro assump_315 assump_316 =>
      cases assump_316
      case intro assump_319 assump_320 =>
        cases assump_319
        case inl assump_321 =>
          cases assump_320
          case inl assump_325 =>
            have assump_403 : ((False → False) ∧ (True ∨ p5)) := by
              apply And.intro
              intro assump_332
              apply False.elim assump_332
              apply Or.inl
              apply True.intro
            let assump_331 := assump_315 assump_403
            apply False.elim assump_331
          case inr assump_326 =>
            cases assump_326
            case inl assump_338 =>
              have assump_404 : ((False → False) ∧ (True ∨ p5)) := by
                apply And.intro
                intro assump_345
                apply False.elim assump_345
                apply Or.inl
                apply True.intro
              let assump_344 := assump_315 assump_404
              apply False.elim assump_344
            case inr assump_339 =>
              apply False.elim assump_339
        case inr assump_322 =>
          cases assump_322
          case inl assump_353 =>
            cases assump_320
            case inl assump_357 =>
              have assump_405 : ((False → False) ∧ (True ∨ p5)) := by
                apply And.intro
                intro assump_364
                apply False.elim assump_364
                apply Or.inl
                apply True.intro
              let assump_363 := assump_315 assump_405
              apply False.elim assump_363
            case inr assump_358 =>
              cases assump_358
              case inl assump_370 =>
                have assump_406 : ((False → False) ∧ (True ∨ p5)) := by
                  apply And.intro
                  intro assump_377
                  apply False.elim assump_377
                  apply Or.inl
                  apply True.intro
                let assump_376 := assump_315 assump_406
                apply False.elim assump_376
              case inr assump_371 =>
                apply False.elim assump_371
          case inr assump_354 =>
            apply False.elim assump_354


variable (p4 p0 p7 p6 p1 p3 : Prop)
theorem file26_91443 : (((((True ∨ False) → False) ∧ ((p4 ∨ p0) ∧ (p7 → False))) → False) ∨ ((((p1 → p6) → False) → ((p4 ∨ p0) ∧ (p0 → p7))) ∧ (((p0 ∨ p3) → False) ∨ ((p6 → False) ∨ (p1 → False))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        have assump_30 : (True ∨ False) := by
          apply Or.inl
          apply True.intro
        let assump_16 := assump_2 assump_30
        apply False.elim assump_16
      case inr assump_9 =>
        have assump_31 : (True ∨ False) := by
          apply Or.inl
          apply True.intro
        let assump_26 := assump_2 assump_31
        apply False.elim assump_26


variable (p3 p4 p6 p0 : Prop)
theorem file26_92242 : (((((p6 ∨ p3) → (False → False)) → False) → False) ∨ ((((True → False) → (False ∨ p3)) ∧ ((p0 → False) ∧ (p4 → False))) → False)) := by
  apply Or.inl
  intro assump_14
  have assump_25 : ((p6 ∨ p3) → (False → False)) := by
    intro assump_18
    intro assump_19
    apply False.elim assump_19
  let assump_17 := assump_14 assump_25
  apply False.elim assump_17


variable (p7 p2 p5 p1 p6 p4 p0 : Prop)
theorem file26_92668 : (((((p7 → p1) ∨ (p5 → False)) ∨ ((p1 ∧ p6) ∧ (p2 ∨ p5))) ∨ (((True ∨ p0) ∨ (p7 → True)) ∧ ((p4 → False) → (False → False)))) → ((((p6 → p2) ∨ (False → False)) → ((p0 → p5) → False)) → (((p4 ∨ True) ∨ (p4 ∨ p2)) ∨ ((p5 → False) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    cases assump_5
    case inl assump_7 =>
      cases assump_7
      case inl assump_9 =>
        apply Or.inl
        apply Or.inl
        apply Or.inr
        apply True.intro
      case inr assump_10 =>
        apply Or.inl
        apply Or.inl
        apply Or.inr
        apply True.intro
    case inr assump_8 =>
      cases assump_8
      case intro assump_15 assump_16 =>
        cases assump_15
        case intro assump_17 assump_18 =>
          cases assump_16
          case inl assump_23 =>
            apply Or.inl
            apply Or.inl
            apply Or.inr
            apply True.intro
          case inr assump_24 =>
            apply Or.inl
            apply Or.inl
            apply Or.inr
            apply True.intro
  case inr assump_6 =>
    cases assump_6
    case intro assump_29 assump_30 =>
      cases assump_29
      case inl assump_31 =>
        cases assump_31
        case inl assump_33 =>
          apply Or.inl
          apply Or.inl
          apply Or.inr
          apply True.intro
        case inr assump_34 =>
          apply Or.inl
          apply Or.inl
          apply Or.inr
          apply True.intro
      case inr assump_32 =>
        apply Or.inl
        apply Or.inl
        apply Or.inr
        apply True.intro


variable (p2 p0 p6 p3 p5 p4 p1 : Prop)
theorem file26_94318 : ((((((p4 → False) ∨ (p6 → False)) ∨ ((p5 → False) → False)) → (((True ∨ p0) ∨ (p3 → False)) ∧ ((p5 → False) → False))) ∧ ((((p3 ∧ False) → False) → False) ∧ (((True ∧ p2) → False) ∧ ((p5 ∧ p5) → (p1 ∧ p1))))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_7
    case intro assump_10 assump_11 =>
      cases assump_11
      case intro assump_14 assump_15 =>
        have assump_33 : ((p3 ∧ False) → False) := by
          intro assump_23
          cases assump_23
          case intro assump_24 assump_25 =>
            apply False.elim assump_25
        let assump_22 := assump_10 assump_33
        apply False.elim assump_22


variable (p1 p5 p0 p2 p6 p7 : Prop)
theorem file26_95058 : ((((((p1 ∨ p2) ∧ (False → p6)) → ((p0 ∧ p1) → (p5 ∨ p1))) → (((p1 ∨ True) ∨ (p5 ∧ p7)) ∨ ((p7 ∧ p2) → (True → False)))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p1 ∨ p2) ∧ (False → p6)) → ((p0 ∧ p1) → (p5 ∨ p1))) → (((p1 ∨ True) ∨ (p5 ∧ p7)) ∨ ((p7 ∧ p2) → (True → False)))) := by
    intro assump_5
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p0 p4 p6 p2 p1 p5 p7 p3 : Prop)
theorem file26_95584 : (((((p2 → p3) ∨ (p5 ∨ p2)) ∨ ((p2 ∧ p1) ∧ (p0 → False))) ∧ (((p3 ∨ True) → False) ∧ ((p4 ∧ p5) ∧ (p7 → p6)))) → ((((False → False) → False) ∨ ((p4 → p5) → (True → p1))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_9
        case inl assump_11 =>
          cases assump_8
          case intro assump_15 assump_16 =>
            cases assump_16
            case intro assump_19 assump_20 =>
              cases assump_19
              case intro assump_21 assump_22 =>
                have assump_225 : (p3 ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_32 := assump_15 assump_225
                apply False.elim assump_32
        case inr assump_12 =>
          cases assump_12
          case inl assump_36 =>
            cases assump_8
            case intro assump_40 assump_41 =>
              cases assump_41
              case intro assump_44 assump_45 =>
                cases assump_44
                case intro assump_46 assump_47 =>
                  have assump_226 : (p3 ∨ True) := by
                    apply Or.inr
                    apply True.intro
                  let assump_57 := assump_40 assump_226
                  apply False.elim assump_57
          case inr assump_37 =>
            cases assump_8
            case intro assump_63 assump_64 =>
              cases assump_64
              case intro assump_67 assump_68 =>
                cases assump_67
                case intro assump_69 assump_70 =>
                  have assump_227 : (p3 ∨ True) := by
                    apply Or.inr
                    apply True.intro
                  let assump_80 := assump_63 assump_227
                  apply False.elim assump_80
      case inr assump_10 =>
        cases assump_10
        case intro assump_84 assump_85 =>
          cases assump_84
          case intro assump_86 assump_87 =>
            cases assump_8
            case intro assump_94 assump_95 =>
              cases assump_95
              case intro assump_98 assump_99 =>
                cases assump_98
                case intro assump_100 assump_101 =>
                  have assump_228 : (p3 ∨ True) := by
                    apply Or.inr
                    apply True.intro
                  let assump_111 := assump_94 assump_228
                  apply False.elim assump_111
  case inr assump_4 =>
    cases assump_1
    case intro assump_117 assump_118 =>
      cases assump_117
      case inl assump_119 =>
        cases assump_119
        case inl assump_121 =>
          cases assump_118
          case intro assump_125 assump_126 =>
            cases assump_126
            case intro assump_129 assump_130 =>
              cases assump_129
              case intro assump_131 assump_132 =>
                have assump_229 : (p3 ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_142 := assump_125 assump_229
                apply False.elim assump_142
        case inr assump_122 =>
          cases assump_122
          case inl assump_146 =>
            cases assump_118
            case intro assump_150 assump_151 =>
              cases assump_151
              case intro assump_154 assump_155 =>
                cases assump_154
                case intro assump_156 assump_157 =>
                  have assump_230 : (p3 ∨ True) := by
                    apply Or.inr
                    apply True.intro
                  let assump_167 := assump_150 assump_230
                  apply False.elim assump_167
          case inr assump_147 =>
            cases assump_118
            case intro assump_173 assump_174 =>
              cases assump_174
              case intro assump_177 assump_178 =>
                cases assump_177
                case intro assump_179 assump_180 =>
                  have assump_231 : (p3 ∨ True) := by
                    apply Or.inr
                    apply True.intro
                  let assump_190 := assump_173 assump_231
                  apply False.elim assump_190
      case inr assump_120 =>
        cases assump_120
        case intro assump_194 assump_195 =>
          cases assump_194
          case intro assump_196 assump_197 =>
            cases assump_118
            case intro assump_204 assump_205 =>
              cases assump_205
              case intro assump_208 assump_209 =>
                cases assump_208
                case intro assump_210 assump_211 =>
                  have assump_232 : (p3 ∨ True) := by
                    apply Or.inr
                    apply True.intro
                  let assump_221 := assump_204 assump_232
                  apply False.elim assump_221


variable (p5 p1 p4 p3 p0 p2 p6 p7 : Prop)
theorem file26_100510 : (((((p0 ∨ p3) ∧ (p1 → False)) → ((p3 ∨ p5) ∧ (p7 ∧ True))) → (((p3 ∧ p3) → (p0 → False)) ∨ ((p7 → p3) ∧ (False ∨ p6)))) → ((((p3 ∧ p1) ∧ (p6 ∨ p4)) ∧ ((False ∧ p4) ∨ (p1 → p2))) ∨ (((p7 ∨ p2) ∧ (p7 ∧ p4)) → ((True ∨ p3) ∨ (p0 ∨ p7))))) := by
  intro assump_1
  apply Or.inr
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      cases assump_6
      case intro assump_11 assump_12 =>
        apply Or.inl
        apply Or.inl
        apply True.intro
    case inr assump_8 =>
      cases assump_6
      case intro assump_19 assump_20 =>
        apply Or.inl
        apply Or.inl
        apply True.intro


variable (p3 p1 p6 p0 p5 : Prop)
theorem file26_101234 : ((((((p5 ∨ p0) → (False → p3)) ∨ ((p1 ∧ p0) ∧ (p3 ∨ p1))) ∧ (((p5 ∨ p6) ∧ (False ∧ True)) → False)) → False) → False) := by
  intro assump_1
  have assump_29 : ((((p5 ∨ p0) → (False → p3)) ∨ ((p1 ∧ p0) ∧ (p3 ∨ p1))) ∧ (((p5 ∨ p6) ∧ (False ∧ True)) → False)) := by
    apply And.intro
    apply Or.inl
    intro assump_5
    intro assump_6
    apply False.elim assump_6
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      cases assump_10
      case inl assump_12 =>
        cases assump_11
        case intro assump_16 assump_17 =>
          apply False.elim assump_16
      case inr assump_13 =>
        cases assump_11
        case intro assump_22 assump_23 =>
          apply False.elim assump_22
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p6 p1 p2 p7 p4 : Prop)
theorem file26_102085 : ((((((False → p7) → False) → ((True ∧ p2) → (p4 ∨ False))) ∨ (((p1 → False) ∨ (p2 → False)) ∨ ((p7 ∧ p7) ∧ (p6 → p1)))) → False) → False) := by
  intro assump_1
  have assump_25 : ((((False → p7) → False) → ((True ∧ p2) → (p4 ∨ False))) ∨ (((p1 → False) ∨ (p2 → False)) ∨ ((p7 ∧ p7) ∧ (p6 → p1)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      have assump_26 : (False → p7) := by
        intro assump_16
        apply False.elim assump_16
      let assump_15 := assump_5 assump_26
      apply False.elim assump_15
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p2 p4 p7 p5 p0 p3 : Prop)
theorem file26_102800 : ((((((p0 ∨ False) ∧ (True ∧ p4)) ∧ ((p0 → False) ∨ (True ∨ p5))) ∨ (((p2 → False) ∧ (p5 → False)) → ((p2 → False) ∨ (p0 → p7)))) ∧ ((((True ∨ p3) ∧ (True ∨ False)) ∨ ((p5 → False) ∧ (p5 → p3))) → False)) → False) := by
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
            cases assump_9
            case intro assump_14 assump_15 =>
              cases assump_7
              case inl assump_20 =>
                have assump_58 : (((True ∨ p3) ∧ (True ∨ False)) ∨ ((p5 → False) ∧ (p5 → p3))) := by
                  apply Or.inl
                  apply And.intro
                  apply Or.inl
                  apply True.intro
                  apply Or.inl
                  apply True.intro
                let assump_26 := assump_3 assump_58
                apply False.elim assump_26
              case inr assump_21 =>
                cases assump_21
                case inl assump_30 =>
                  have assump_59 : (((True ∨ p3) ∧ (True ∨ False)) ∨ ((p5 → False) ∧ (p5 → p3))) := by
                    apply Or.inl
                    apply And.intro
                    apply Or.inl
                    apply True.intro
                    apply Or.inl
                    apply True.intro
                  let assump_36 := assump_3 assump_59
                  apply False.elim assump_36
                case inr assump_31 =>
                  have assump_60 : (((True ∨ p3) ∧ (True ∨ False)) ∨ ((p5 → False) ∧ (p5 → p3))) := by
                    apply Or.inl
                    apply And.intro
                    apply Or.inl
                    apply True.intro
                    apply Or.inl
                    apply True.intro
                  let assump_44 := assump_3 assump_60
                  apply False.elim assump_44
          case inr assump_11 =>
            apply False.elim assump_11
    case inr assump_5 =>
      have assump_61 : (((True ∨ p3) ∧ (True ∨ False)) ∨ ((p5 → False) ∧ (p5 → p3))) := by
        apply Or.inl
        apply And.intro
        apply Or.inl
        apply True.intro
        apply Or.inl
        apply True.intro
      let assump_54 := assump_3 assump_61
      apply False.elim assump_54


variable (p3 p1 p7 p5 p2 p0 p4 p6 : Prop)
theorem file26_105272 : (((((p6 → p2) → (False ∨ p1)) ∧ ((False → p0) ∨ (p1 ∨ False))) → False) → ((((p1 → p4) ∨ (p3 ∨ p3)) ∨ ((p0 → False) ∨ (p7 ∨ p7))) ∨ (((p1 ∧ True) ∨ (p6 ∨ p5)) ∧ ((p2 ∨ p6) ∨ (False → p0))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_4
  have assump_18 : (((p6 → p2) → (False ∨ p1)) ∧ ((False → p0) ∨ (p1 ∨ False))) := by
    apply And.intro
    intro assump_9
    apply Or.inr
    exact assump_4
    apply Or.inl
    intro assump_12
    apply False.elim assump_12
  let assump_8 := assump_1 assump_18
  apply False.elim assump_8


variable (p4 p2 p7 p1 p3 p5 p0 : Prop)
theorem file26_105905 : (((((p2 ∧ p1) ∧ (p5 ∨ True)) ∨ ((p2 ∧ p5) → (p3 → p5))) ∧ (((p4 ∧ False) ∧ (p5 ∧ p7)) → ((p1 ∧ p1) → False))) ∨ ((((p7 ∨ p5) → (p7 → False)) → ((p0 → False) ∨ (p0 ∨ p4))) ∧ (((p0 → False) ∧ (p7 → False)) → ((p7 → p5) ∧ (p7 → p5))))) := by
  apply Or.inl
  apply And.intro
  apply Or.inr
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    exact assump_6
  intro assump_11
  intro assump_12
  cases assump_12
  case intro assump_13 assump_14 =>
    cases assump_11
    case intro assump_19 assump_20 =>
      cases assump_19
      case intro assump_21 assump_22 =>
        apply False.elim assump_22


variable (p0 p4 p7 p1 p2 p6 : Prop)
theorem file26_106601 : ((((((p2 → False) → False) ∨ ((p6 → p6) ∧ (p4 ∧ p6))) → (((p0 → False) → False) ∨ ((False → False) → (False ∨ True)))) ∧ ((((True → p7) → (p7 ∨ p2)) ∧ ((p1 ∧ False) → False)) ∧ (((p1 → False) → False) ∧ ((p4 → False) ∧ (p1 → False))))) → False) := by
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
            have assump_38 : (p1 → False) := by
              intro assump_27
              have assump_39 : p1 := by
                exact assump_27
              let assump_31 := assump_19 assump_39
              apply False.elim assump_31
            let assump_26 := assump_14 assump_38
            apply False.elim assump_26


variable (p7 p2 p5 p6 p4 p1 p0 : Prop)
theorem file26_107562 : (((((p7 → False) ∧ (p1 ∧ False)) → ((p7 → False) ∨ (p2 → False))) → False) → ((((p6 → False) ∨ (True ∨ p4)) ∧ ((p5 → False) → (p5 ∧ p7))) ∧ (((p0 ∧ False) → False) → False))) := by
  intro assump_28
  apply And.intro
  apply And.intro
  apply Or.inl
  intro assump_31
  have assump_109 : (((p7 → False) ∧ (p1 ∧ False)) → ((p7 → False) ∨ (p2 → False))) := by
    intro assump_36
    cases assump_36
    case intro assump_37 assump_38 =>
      cases assump_38
      case intro assump_41 assump_42 =>
        apply False.elim assump_42
  let assump_35 := assump_28 assump_109
  apply False.elim assump_35
  intro assump_50
  apply And.intro
  have assump_110 : (((p7 → False) ∧ (p1 ∧ False)) → ((p7 → False) ∨ (p2 → False))) := by
    intro assump_56
    cases assump_56
    case intro assump_57 assump_58 =>
      cases assump_58
      case intro assump_61 assump_62 =>
        apply False.elim assump_62
  let assump_55 := assump_28 assump_110
  apply False.elim assump_55
  have assump_111 : (((p7 → False) ∧ (p1 ∧ False)) → ((p7 → False) ∨ (p2 → False))) := by
    intro assump_75
    cases assump_75
    case intro assump_76 assump_77 =>
      cases assump_77
      case intro assump_80 assump_81 =>
        apply False.elim assump_81
  let assump_74 := assump_28 assump_111
  apply False.elim assump_74
  intro assump_89
  have assump_112 : (((p7 → False) ∧ (p1 ∧ False)) → ((p7 → False) ∨ (p2 → False))) := by
    intro assump_95
    cases assump_95
    case intro assump_96 assump_97 =>
      cases assump_97
      case intro assump_100 assump_101 =>
        apply False.elim assump_101
  let assump_94 := assump_28 assump_112
  apply False.elim assump_94


variable (p7 p5 p0 p4 p6 p3 p2 p1 : Prop)
theorem file26_109289 : (((((p3 ∧ p1) → (p5 ∨ p3)) ∨ ((p1 ∨ p6) ∨ (p6 → p2))) ∨ (((p0 ∨ p4) ∨ (p3 → p2)) → ((p5 → False) → (p6 ∨ p7)))) ∨ ((((False ∧ p3) ∨ (p1 → p4)) → ((False ∨ p6) ∨ (p2 ∧ p4))) ∨ (((p7 → False) ∨ (p2 ∧ p7)) ∧ ((p0 ∨ False) ∧ (p3 ∧ p3))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inr
    exact assump_2


variable (p3 p6 p7 p1 p4 p0 p5 p2 : Prop)
theorem file26_109745 : (((((p6 ∨ True) ∧ (p5 ∧ p5)) ∨ ((p5 → False) → (p6 ∨ p7))) ∧ (((p0 → False) ∧ (p5 ∧ p6)) → ((p2 ∧ p3) ∨ (p0 ∨ p7)))) → ((((p3 → p6) → (p2 ∨ p1)) → ((p5 ∧ p2) → (False → False))) ∨ (((False ∧ p4) ∨ (p4 ∨ p0)) ∨ ((p5 ∨ p1) ∧ (p7 ∧ p5))))) := by
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
            apply Or.inl
            intro assump_20
            intro assump_21
            intro assump_22
            apply False.elim assump_22
        case inr assump_9 =>
          cases assump_7
          case intro assump_27 assump_28 =>
            apply Or.inl
            intro assump_35
            intro assump_36
            intro assump_37
            apply False.elim assump_37
    case inr assump_5 =>
      apply Or.inl
      intro assump_44
      intro assump_45
      intro assump_46
      apply False.elim assump_46


variable (p7 p3 p1 p0 p5 p2 p6 p4 : Prop)
theorem file26_110883 : (((((p1 → False) ∨ (p6 ∧ p6)) → False) → (((True → False) ∨ (p4 → False)) ∨ ((p5 ∨ p3) ∧ (p7 → False)))) → ((((p5 → True) ∨ (p4 → False)) ∨ ((p2 ∧ p6) → False)) ∨ (((p4 → False) ∨ (p1 ∧ p5)) ∧ ((p3 ∧ p7) → (p0 → p1))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_4
  apply True.intro


variable (p6 p1 p0 : Prop)
theorem file26_111258 : (((((False ∧ False) → False) ∨ ((p0 ∧ p1) ∨ (p6 → False))) → False) → False) := by
  intro assump_1
  have assump_13 : (((False ∧ False) → False) ∨ ((p0 ∧ p1) ∨ (p6 → False))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p6 p7 p5 p3 p4 p1 p2 : Prop)
theorem file26_111691 : (((((p3 → False) → (p2 → False)) ∧ ((p7 → False) → (p4 ∨ True))) → (((p7 → p1) ∨ (p6 ∧ p5)) ∨ ((p7 ∨ p3) ∧ (p1 → p3)))) → ((((p2 → False) → False) → ((False → p6) ∨ (p7 ∨ p2))) ∨ (((p7 ∧ p6) ∨ (p3 ∨ p7)) → False))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  apply Or.inl
  intro assump_7
  apply False.elim assump_7


variable (p0 p1 p2 p7 p6 p5 p4 : Prop)
theorem file26_112084 : ((((((p4 ∧ p5) → (False ∨ p5)) → False) → (((p5 → True) ∨ (p6 ∨ p5)) → False)) → ((((False ∧ p0) → (p7 ∨ False)) ∨ ((p0 → p2) ∧ (p1 ∨ False))) → False)) → False) := by
  intro assump_1
  have assump_65 : ((((p4 ∧ p5) → (False ∨ p5)) → False) → (((p5 → True) ∨ (p6 ∨ p5)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      have assump_66 : ((p4 ∧ p5) → (False ∨ p5)) := by
        intro assump_14
        cases assump_14
        case intro assump_15 assump_16 =>
          apply Or.inr
          exact assump_16
      let assump_13 := assump_5 assump_66
      apply False.elim assump_13
    case inr assump_8 =>
      cases assump_8
      case inl assump_24 =>
        have assump_67 : ((p4 ∧ p5) → (False ∨ p5)) := by
          intro assump_31
          cases assump_31
          case intro assump_32 assump_33 =>
            apply Or.inr
            exact assump_33
        let assump_30 := assump_5 assump_67
        apply False.elim assump_30
      case inr assump_25 =>
        have assump_68 : ((p4 ∧ p5) → (False ∨ p5)) := by
          intro assump_46
          cases assump_46
          case intro assump_47 assump_48 =>
            apply Or.inr
            exact assump_48
        let assump_45 := assump_5 assump_68
        apply False.elim assump_45
  let assump_4 := assump_1 assump_65
  have assump_69 : (((False ∧ p0) → (p7 ∨ False)) ∨ ((p0 → p2) ∧ (p1 ∨ False))) := by
    apply Or.inl
    intro assump_57
    cases assump_57
    case intro assump_58 assump_59 =>
      apply False.elim assump_58
  let assump_56 := assump_4 assump_69
  apply False.elim assump_56


variable (p4 p5 p0 p2 p1 : Prop)
theorem file26_113772 : ((((((False → False) → False) → False) → False) ∧ ((((p4 ∧ p5) → False) ∧ ((p4 ∧ p4) → (p1 ∨ False))) ∧ (((p0 ∨ p5) → False) ∨ ((p0 ∧ False) → (p5 ∧ p2))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case inl assump_14 =>
          have assump_54 : (((False → False) → False) → False) := by
            intro assump_22
            have assump_55 : (False → False) := by
              intro assump_26
              apply False.elim assump_26
            let assump_25 := assump_22 assump_55
            apply False.elim assump_25
          let assump_21 := assump_2 assump_54
          apply False.elim assump_21
        case inr assump_15 =>
          have assump_56 : (((False → False) → False) → False) := by
            intro assump_41
            have assump_57 : (False → False) := by
              intro assump_45
              apply False.elim assump_45
            let assump_44 := assump_41 assump_57
            apply False.elim assump_44
          let assump_40 := assump_2 assump_56
          apply False.elim assump_40


variable (p0 p4 p5 : Prop)
theorem file26_115040 : (((((p0 ∧ p4) ∧ (p4 → False)) → ((p5 → False) → False)) → False) → False) := by
  intro assump_1
  have assump_26 : (((p0 ∧ p4) ∧ (p4 → False)) → ((p5 → False) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        have assump_27 : p4 := by
          exact assump_12
        let assump_19 := assump_10 assump_27
        apply False.elim assump_19
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p7 p2 p4 p6 p3 p0 p5 p1 : Prop)
theorem file26_115642 : ((((((p7 → p2) ∨ (p6 → p0)) → ((p0 → p1) ∧ (True → False))) ∧ (((p3 → p4) ∧ (p7 → False)) ∧ ((False ∧ p6) ∧ (p1 → False)))) ∧ ((((p2 → p1) ∨ (False → p2)) → False) → (((p1 ∧ p4) ∨ (p5 ∧ False)) ∧ ((True → False) ∨ (False ∨ p2))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_9
          case intro assump_16 assump_17 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              apply False.elim assump_18


variable (p6 p0 p1 p5 p3 p4 : Prop)
theorem file26_116379 : ((((((p4 ∨ p0) ∨ (p3 → False)) ∨ ((p4 ∨ True) ∨ (p4 ∧ False))) → (((p6 → p6) ∨ (p1 ∨ p5)) ∧ ((p1 ∨ p1) ∨ (False → p1)))) → False) → False) := by
  intro assump_1
  have assump_91 : ((((p4 ∨ p0) ∨ (p3 → False)) ∨ ((p4 ∨ True) ∨ (p4 ∧ False))) → (((p6 → p6) ∨ (p1 ∨ p5)) ∧ ((p1 ∨ p1) ∨ (False → p1)))) := by
    intro assump_5
    apply And.intro
    cases assump_5
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          apply Or.inl
          intro assump_14
          exact assump_14
        case inr assump_11 =>
          apply Or.inl
          intro assump_19
          exact assump_19
      case inr assump_9 =>
        apply Or.inl
        intro assump_24
        exact assump_24
    case inr assump_7 =>
      cases assump_7
      case inl assump_27 =>
        cases assump_27
        case inl assump_29 =>
          apply Or.inl
          intro assump_33
          exact assump_33
        case inr assump_30 =>
          apply Or.inl
          intro assump_38
          exact assump_38
      case inr assump_28 =>
        cases assump_28
        case intro assump_41 assump_42 =>
          apply False.elim assump_42
    cases assump_5
    case inl assump_47 =>
      cases assump_47
      case inl assump_49 =>
        cases assump_49
        case inl assump_51 =>
          apply Or.inr
          intro assump_55
          apply False.elim assump_55
        case inr assump_52 =>
          apply Or.inr
          intro assump_60
          apply False.elim assump_60
      case inr assump_50 =>
        apply Or.inr
        intro assump_65
        apply False.elim assump_65
    case inr assump_48 =>
      cases assump_48
      case inl assump_68 =>
        cases assump_68
        case inl assump_70 =>
          apply Or.inr
          intro assump_74
          apply False.elim assump_74
        case inr assump_71 =>
          apply Or.inr
          intro assump_79
          apply False.elim assump_79
      case inr assump_69 =>
        cases assump_69
        case intro assump_82 assump_83 =>
          apply False.elim assump_83
  let assump_4 := assump_1 assump_91
  apply False.elim assump_4


