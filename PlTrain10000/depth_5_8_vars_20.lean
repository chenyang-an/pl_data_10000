variable (p2 p3 p1 p7 p6 p4 p0 : Prop)
theorem file20_47 : ((((((p3 → p6) → (False ∧ p6)) → ((p3 ∨ True) ∨ (p7 → False))) ∨ (((p4 → p6) → (p2 → False)) ∨ ((p6 ∧ p0) ∧ (p1 → True)))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p3 → p6) → (False ∧ p6)) → ((p3 ∨ True) ∨ (p7 → False))) ∨ (((p4 → p6) → (p2 → False)) ∨ ((p6 ∧ p0) ∧ (p1 → True)))) := by
    apply Or.inl
    intro assump_5
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p4 p7 p5 p1 : Prop)
theorem file20_567 : ((((((p1 → True) → (p4 ∨ p7)) ∧ ((p5 ∨ p1) ∧ (False ∧ True))) → False) → False) → False) := by
  intro assump_1
  have assump_29 : ((((p1 → True) → (p4 ∨ p7)) ∧ ((p5 ∨ p1) ∧ (False ∧ True))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
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


variable (p0 p6 p7 p3 p5 p2 p1 : Prop)
theorem file20_1338 : (((((False → False) → (p3 ∧ p6)) → ((p7 ∨ p2) → False)) → (((False ∨ False) ∧ (p0 ∧ p2)) → False)) ∨ ((((p6 → p5) → (True ∧ p0)) ∧ ((p1 ∧ p7) → (p1 ∧ False))) ∨ (((True → False) → (p0 → False)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      apply False.elim assump_5
    case inr assump_6 =>
      apply False.elim assump_6


variable (p3 p6 p1 p0 p4 p7 p2 : Prop)
theorem file20_1845 : (((((p4 ∨ False) → False) ∧ ((p6 ∧ p4) ∧ (False → False))) → False) ∨ ((((p7 → False) ∨ (p3 ∧ p2)) → ((p3 → False) ∧ (p0 → False))) ∨ (((p3 ∨ p0) ∨ (p1 ∧ p2)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        have assump_23 : (p4 ∨ False) := by
          apply Or.inl
          exact assump_9
        let assump_19 := assump_2 assump_23
        apply False.elim assump_19


variable (p4 p0 p3 : Prop)
theorem file20_2440 : (((((True ∨ True) ∨ (p4 ∨ p0)) ∧ ((p4 ∧ p0) ∧ (p3 → False))) ∧ (((p4 → False) → False) → False)) → False) := by
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
          case intro assump_12 assump_13 =>
            cases assump_12
            case intro assump_14 assump_15 =>
              have assump_112 : ((p4 → False) → False) := by
                intro assump_25
                have assump_113 : p4 := by
                  exact assump_14
                let assump_28 := assump_25 assump_113
                apply False.elim assump_28
              let assump_24 := assump_3 assump_112
              apply False.elim assump_24
        case inr assump_9 =>
          cases assump_5
          case intro assump_37 assump_38 =>
            cases assump_37
            case intro assump_39 assump_40 =>
              have assump_114 : ((p4 → False) → False) := by
                intro assump_50
                have assump_115 : p4 := by
                  exact assump_39
                let assump_53 := assump_50 assump_115
                apply False.elim assump_53
              let assump_49 := assump_3 assump_114
              apply False.elim assump_49
      case inr assump_7 =>
        cases assump_7
        case inl assump_60 =>
          cases assump_5
          case intro assump_64 assump_65 =>
            cases assump_64
            case intro assump_66 assump_67 =>
              have assump_116 : ((p4 → False) → False) := by
                intro assump_77
                have assump_117 : p4 := by
                  exact assump_66
                let assump_80 := assump_77 assump_117
                apply False.elim assump_80
              let assump_76 := assump_3 assump_116
              apply False.elim assump_76
        case inr assump_61 =>
          cases assump_5
          case intro assump_89 assump_90 =>
            cases assump_89
            case intro assump_91 assump_92 =>
              have assump_118 : ((p4 → False) → False) := by
                intro assump_102
                have assump_119 : p4 := by
                  exact assump_91
                let assump_105 := assump_102 assump_119
                apply False.elim assump_105
              let assump_101 := assump_3 assump_118
              apply False.elim assump_101


variable (p6 p4 : Prop)
theorem file20_4976 : (((((False ∧ False) → False) ∨ ((p4 → p6) ∨ (False → True))) → False) → False) := by
  intro assump_35
  have assump_47 : (((False ∧ False) → False) ∨ ((p4 → p6) ∨ (False → True))) := by
    apply Or.inl
    intro assump_39
    cases assump_39
    case intro assump_40 assump_41 =>
      apply False.elim assump_40
  let assump_38 := assump_35 assump_47
  apply False.elim assump_38


variable (p5 p6 p7 p1 p2 p0 p3 : Prop)
theorem file20_5422 : (((((True → False) → (p7 → p5)) → False) → (((False → p0) ∧ (p3 → False)) → ((p6 ∧ p2) → (p5 ∨ p2)))) ∨ ((((p7 ∨ False) → False) → ((False ∧ p1) → (p2 ∧ p2))) → (((p0 ∨ p7) → False) ∧ ((p1 ∧ p0) → (p6 → False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_2
    case intro assump_10 assump_11 =>
      apply Or.inr
      exact assump_5


variable (p6 p7 p1 p2 p3 p4 p5 : Prop)
theorem file20_5919 : (((((p7 ∨ p1) ∨ (p6 ∧ p5)) ∧ ((p3 → False) ∧ (p3 ∧ p7))) → (((p7 → p3) → False) ∨ ((p4 ∧ p1) → (False ∨ p1)))) → ((((False ∧ p2) ∧ (p1 ∧ p4)) → False) ∨ (((False ∨ p2) ∨ (p5 → False)) ∧ ((False → p7) ∨ (p6 ∨ p7))))) := by
  intro assump_5
  apply Or.inl
  intro assump_8
  cases assump_8
  case intro assump_9 assump_10 =>
    cases assump_9
    case intro assump_11 assump_12 =>
      apply False.elim assump_11


variable (p6 p3 p7 p4 p5 : Prop)
theorem file20_6389 : (((((p5 → p3) ∧ (True → False)) → ((p4 ∨ p3) ∧ (p7 → False))) → False) → ((((p6 → p6) → False) ∧ ((p4 ∨ p3) → False)) ∨ (((p4 → False) ∨ (p4 ∨ p4)) ∨ ((p4 → True) → (True ∨ p6))))) := by
  intro assump_1
  apply Or.inl
  apply And.intro
  intro assump_4
  have assump_93 : (((p5 → p3) ∧ (True → False)) → ((p4 ∨ p3) ∧ (p7 → False))) := by
    intro assump_9
    apply And.intro
    cases assump_9
    case intro assump_10 assump_11 =>
      have assump_94 : True := by
        apply True.intro
      let assump_16 := assump_11 assump_94
      apply False.elim assump_16
    intro assump_20
    cases assump_9
    case intro assump_23 assump_24 =>
      have assump_95 : True := by
        apply True.intro
      let assump_29 := assump_24 assump_95
      apply False.elim assump_29
  let assump_8 := assump_1 assump_93
  apply False.elim assump_8
  intro assump_36
  cases assump_36
  case inl assump_37 =>
    have assump_96 : (((p5 → p3) ∧ (True → False)) → ((p4 ∨ p3) ∧ (p7 → False))) := by
      intro assump_43
      apply And.intro
      cases assump_43
      case intro assump_44 assump_45 =>
        apply Or.inl
        exact assump_37
      intro assump_50
      cases assump_43
      case intro assump_53 assump_54 =>
        have assump_97 : True := by
          apply True.intro
        let assump_59 := assump_54 assump_97
        apply False.elim assump_59
    let assump_42 := assump_1 assump_96
    apply False.elim assump_42
  case inr assump_38 =>
    have assump_98 : (((p5 → p3) ∧ (True → False)) → ((p4 ∨ p3) ∧ (p7 → False))) := by
      intro assump_70
      apply And.intro
      cases assump_70
      case intro assump_71 assump_72 =>
        apply Or.inr
        exact assump_38
      intro assump_77
      cases assump_70
      case intro assump_80 assump_81 =>
        have assump_99 : True := by
          apply True.intro
        let assump_86 := assump_81 assump_99
        apply False.elim assump_86
    let assump_69 := assump_1 assump_98
    apply False.elim assump_69


variable (p4 p7 p1 p5 p3 p0 : Prop)
theorem file20_8452 : ((((((False → p0) → False) ∧ ((p7 ∨ p5) ∨ (p7 ∨ p4))) → (((p4 ∧ p0) → (p4 → False)) → ((p4 ∧ p1) ∨ (p3 ∨ p3)))) → False) → False) := by
  intro assump_1
  have assump_62 : ((((False → p0) → False) ∧ ((p7 ∨ p5) ∨ (p7 ∨ p4))) → (((p4 ∧ p0) → (p4 → False)) → ((p4 ∧ p1) ∨ (p3 ∨ p3)))) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_10
      case inl assump_13 =>
        cases assump_13
        case inl assump_15 =>
          have assump_63 : (False → p0) := by
            intro assump_21
            apply False.elim assump_21
          let assump_20 := assump_9 assump_63
          apply False.elim assump_20
        case inr assump_16 =>
          have assump_64 : (False → p0) := by
            intro assump_31
            apply False.elim assump_31
          let assump_30 := assump_9 assump_64
          apply False.elim assump_30
      case inr assump_14 =>
        cases assump_14
        case inl assump_37 =>
          have assump_65 : (False → p0) := by
            intro assump_43
            apply False.elim assump_43
          let assump_42 := assump_9 assump_65
          apply False.elim assump_42
        case inr assump_38 =>
          have assump_66 : (False → p0) := by
            intro assump_53
            apply False.elim assump_53
          let assump_52 := assump_9 assump_66
          apply False.elim assump_52
  let assump_4 := assump_1 assump_62
  apply False.elim assump_4


variable (p1 p7 p5 p2 p6 p3 : Prop)
theorem file20_9989 : ((((((True ∨ p1) ∨ (p5 ∧ p7)) → False) → (((p2 → p2) ∨ (False → p1)) ∨ ((True → p6) → (False → p3)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((True ∨ p1) ∨ (p5 ∧ p7)) → False) → (((p2 → p2) ∨ (False → p1)) ∨ ((True → p6) → (False → p3)))) := by
    intro assump_5
    apply Or.inl
    apply Or.inl
    intro assump_8
    exact assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p0 p5 p4 p2 p6 p3 : Prop)
theorem file20_10473 : (((((p4 ∧ p3) → (p6 ∨ p5)) ∧ ((p5 → p0) → False)) → (((True → p6) ∧ (p6 ∧ p0)) → False)) ∨ ((((p0 → False) ∧ (False → True)) → ((p6 ∨ p4) → (p2 → False))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      cases assump_1
      case intro assump_13 assump_14 =>
        have assump_26 : (p5 → p0) := by
          intro assump_20
          exact assump_8
        let assump_19 := assump_14 assump_26
        apply False.elim assump_19


variable (p3 p6 p2 p5 p1 p0 p4 p7 : Prop)
theorem file20_11098 : ((((((p0 ∧ p2) ∨ (p4 ∧ p4)) ∧ ((p5 ∧ p0) ∧ (False ∨ p3))) ∧ (((False → p0) ∧ (p6 → p2)) ∨ ((False ∧ True) ∧ (p6 → p7)))) ∧ ((((False → False) → False) → ((p7 ∧ p1) ∧ (p7 → False))) → False)) → False) := by
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
          case intro assump_10 assump_11 =>
            cases assump_7
            case intro assump_16 assump_17 =>
              cases assump_16
              case intro assump_18 assump_19 =>
                cases assump_17
                case inl assump_24 =>
                  apply False.elim assump_24
                case inr assump_25 =>
                  cases assump_5
                  case inl assump_30 =>
                    cases assump_30
                    case intro assump_32 assump_33 =>
                      have assump_152 : (((False → False) → False) → ((p7 ∧ p1) ∧ (p7 → False))) := by
                        intro assump_41
                        apply And.intro
                        apply And.intro
                        have assump_153 : (False → False) := by
                          intro assump_45
                          apply False.elim assump_45
                        let assump_44 := assump_41 assump_153
                        apply False.elim assump_44
                        have assump_154 : (False → False) := by
                          intro assump_54
                          apply False.elim assump_54
                        let assump_53 := assump_41 assump_154
                        apply False.elim assump_53
                        intro assump_60
                        have assump_155 : (False → False) := by
                          intro assump_66
                          apply False.elim assump_66
                        let assump_65 := assump_41 assump_155
                        apply False.elim assump_65
                      let assump_40 := assump_3 assump_152
                      apply False.elim assump_40
                  case inr assump_31 =>
                    cases assump_31
                    case intro assump_75 assump_76 =>
                      cases assump_75
                      case intro assump_77 assump_78 =>
                        apply False.elim assump_77
        case inr assump_9 =>
          cases assump_9
          case intro assump_81 assump_82 =>
            cases assump_7
            case intro assump_87 assump_88 =>
              cases assump_87
              case intro assump_89 assump_90 =>
                cases assump_88
                case inl assump_95 =>
                  apply False.elim assump_95
                case inr assump_96 =>
                  cases assump_5
                  case inl assump_101 =>
                    cases assump_101
                    case intro assump_103 assump_104 =>
                      have assump_156 : (((False → False) → False) → ((p7 ∧ p1) ∧ (p7 → False))) := by
                        intro assump_112
                        apply And.intro
                        apply And.intro
                        have assump_157 : (False → False) := by
                          intro assump_116
                          apply False.elim assump_116
                        let assump_115 := assump_112 assump_157
                        apply False.elim assump_115
                        have assump_158 : (False → False) := by
                          intro assump_125
                          apply False.elim assump_125
                        let assump_124 := assump_112 assump_158
                        apply False.elim assump_124
                        intro assump_131
                        have assump_159 : (False → False) := by
                          intro assump_137
                          apply False.elim assump_137
                        let assump_136 := assump_112 assump_159
                        apply False.elim assump_136
                      let assump_111 := assump_3 assump_156
                      apply False.elim assump_111
                  case inr assump_102 =>
                    cases assump_102
                    case intro assump_146 assump_147 =>
                      cases assump_146
                      case intro assump_148 assump_149 =>
                        apply False.elim assump_148


variable (p1 p3 p0 p5 p6 p4 : Prop)
theorem file20_15654 : (((((p6 → p0) → (False → p3)) → False) → False) ∨ ((((p6 ∧ p4) ∧ (p5 ∨ True)) ∨ ((p0 → p6) ∧ (True ∨ True))) ∨ (((p3 → False) ∨ (p4 ∨ p4)) ∧ ((p6 ∨ p5) ∨ (p1 → False))))) := by
  apply Or.inl
  intro assump_1
  have assump_12 : ((p6 → p0) → (False → p3)) := by
    intro assump_5
    intro assump_6
    apply False.elim assump_6
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p0 p4 p1 p2 : Prop)
theorem file20_16102 : ((((((False → True) ∧ (True → p4)) ∨ ((p2 → False) → False)) → (((p1 → False) → (True → p0)) → ((True ∨ True) ∨ (p1 → p1)))) → False) → False) := by
  intro assump_1
  have assump_22 : ((((False → True) ∧ (True → p4)) ∨ ((p2 → False) → False)) → (((p1 → False) → (True → p0)) → ((True ∨ True) ∨ (p1 → p1)))) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case inl assump_9 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        apply Or.inl
        apply Or.inl
        apply True.intro
    case inr assump_10 =>
      apply Or.inl
      apply Or.inl
      apply True.intro
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p4 p3 p7 p1 p5 p6 : Prop)
theorem file20_16838 : (((((p1 ∧ p3) → False) → ((p6 ∨ False) ∨ (p6 ∨ p6))) → (((p1 ∧ p3) → (True ∧ True)) ∨ ((p4 ∧ False) → (False → False)))) ∨ ((((p5 ∨ p4) ∧ (False → False)) ∨ ((p7 → False) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  apply And.intro
  apply True.intro
  apply True.intro


variable (p6 p5 p7 p3 p2 p4 p1 : Prop)
theorem file20_17218 : (((((p6 ∨ p3) ∧ (False ∧ p7)) → ((p1 → False) ∨ (p5 ∨ p6))) ∨ (((p2 → False) ∧ (p6 ∨ p7)) ∨ ((False ∨ p1) → False))) ∨ ((((p4 → p4) → (p7 ∨ p1)) → False) ∧ (((p3 → False) ∨ (p4 ∨ True)) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        apply False.elim assump_8
    case inr assump_5 =>
      cases assump_3
      case intro assump_14 assump_15 =>
        apply False.elim assump_14


variable (p5 p7 p3 p2 p1 p0 : Prop)
theorem file20_17837 : (((((p7 → p2) ∧ (p3 → p3)) ∧ ((p7 → False) → False)) → (((p7 → False) ∧ (False ∨ False)) ∨ ((p5 ∨ True) ∨ (p0 → p2)))) → ((((p1 ∧ p3) ∨ (p1 → p7)) → False) → (((p2 ∨ p1) ∧ (p7 ∨ p5)) ∨ ((True → False) → (p2 → False))))) := by
  intro assump_1
  intro assump_2
  apply Or.inr
  intro assump_7
  intro assump_8
  have assump_17 : True := by
    apply True.intro
  let assump_13 := assump_7 assump_17
  apply False.elim assump_13


variable (p1 p6 p0 p4 p2 : Prop)
theorem file20_18321 : (((((False ∧ p2) → False) → False) → (((p0 ∧ p1) → (p6 ∧ p1)) → False)) ∨ ((((True ∨ p4) ∨ (p4 → p4)) → False) → (((p2 → False) → False) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  have assump_16 : ((False ∧ p2) → False) := by
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      apply False.elim assump_9
  let assump_7 := assump_1 assump_16
  apply False.elim assump_7


variable (p5 p0 p4 p6 p7 p3 p1 : Prop)
theorem file20_18807 : (((((p6 → p4) → (False ∧ p0)) ∧ ((p1 ∧ p1) → (False ∧ p3))) ∧ (((p6 → p6) ∨ (p0 → p7)) ∧ ((p6 → p6) ∨ (p6 ∨ p1)))) → ((((p3 ∧ p0) → (p0 → p5)) ∧ ((p5 → False) → False)) → (((p5 ∧ p6) → (True → False)) → ((p7 ∨ False) → (p4 → p6))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  intro assump_5
  cases assump_4
  case inl assump_8 =>
    cases assump_2
    case intro assump_14 assump_15 =>
      cases assump_1
      case intro assump_20 assump_21 =>
        cases assump_20
        case intro assump_22 assump_23 =>
          cases assump_21
          case intro assump_28 assump_29 =>
            cases assump_28
            case inl assump_30 =>
              cases assump_29
              case inl assump_34 =>
                have assump_94 : (p6 → p4) := by
                  intro assump_42
                  exact assump_5
                let assump_41 := assump_22 assump_94
                let assump_45 := And.left assump_41
                apply False.elim assump_45
              case inr assump_35 =>
                cases assump_35
                case inl assump_49 =>
                  exact assump_49
                case inr assump_50 =>
                  have assump_95 : (p1 ∧ p1) := by
                    apply And.intro
                    exact assump_50
                    exact assump_50
                  let assump_57 := assump_23 assump_95
                  let assump_58 := And.left assump_57
                  apply False.elim assump_58
            case inr assump_31 =>
              cases assump_29
              case inl assump_64 =>
                have assump_96 : (p6 → p4) := by
                  intro assump_72
                  exact assump_5
                let assump_71 := assump_22 assump_96
                let assump_75 := And.left assump_71
                apply False.elim assump_75
              case inr assump_65 =>
                cases assump_65
                case inl assump_79 =>
                  exact assump_79
                case inr assump_80 =>
                  have assump_97 : (p1 ∧ p1) := by
                    apply And.intro
                    exact assump_80
                    exact assump_80
                  let assump_87 := assump_23 assump_97
                  let assump_88 := And.left assump_87
                  apply False.elim assump_88
  case inr assump_9 =>
    apply False.elim assump_9


variable (p3 p0 p2 p5 p6 p7 p4 p1 : Prop)
theorem file20_21282 : (((((p4 → False) ∨ (p1 → False)) ∧ ((p7 → False) ∧ (True ∨ p4))) → (((p2 → False) ∧ (p5 ∨ p1)) ∨ ((False ∧ p7) ∨ (p0 ∨ p3)))) → ((((False ∧ p7) → False) ∨ ((p5 ∧ p6) ∨ (p6 → False))) ∨ (((False ∨ p7) ∨ (p4 → p2)) → ((p1 ∨ p5) ∧ (p5 ∨ p3))))) := by
  intro assump_54
  apply Or.inl
  apply Or.inl
  intro assump_57
  cases assump_57
  case intro assump_58 assump_59 =>
    apply False.elim assump_58


variable (p1 p4 p2 p7 p5 : Prop)
theorem file20_21738 : (((((p5 → p2) ∧ (p5 ∨ p4)) → ((p7 ∧ True) → (p1 → p7))) → False) → False) := by
  intro assump_1
  have assump_29 : (((p5 → p2) ∧ (p5 ∨ p4)) → ((p7 ∧ True) → (p1 → p7))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      cases assump_5
      case intro assump_16 assump_17 =>
        cases assump_17
        case inl assump_20 =>
          exact assump_10
        case inr assump_21 =>
          exact assump_10
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p7 p2 p3 p6 p4 p0 p5 : Prop)
theorem file20_22353 : (((((p3 ∨ p6) ∧ (False ∨ True)) ∧ ((False ∧ p3) ∧ (p7 → p4))) → False) ∨ ((((p0 ∨ p5) ∨ (p3 → False)) → ((p6 → True) ∧ (p3 ∨ p7))) ∧ (((p0 ∧ p2) ∧ (p7 ∨ p6)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_5
        case inl assump_10 =>
          apply False.elim assump_10
        case inr assump_11 =>
          cases assump_3
          case intro assump_16 assump_17 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              apply False.elim assump_18
      case inr assump_7 =>
        cases assump_5
        case inl assump_24 =>
          apply False.elim assump_24
        case inr assump_25 =>
          cases assump_3
          case intro assump_30 assump_31 =>
            cases assump_30
            case intro assump_32 assump_33 =>
              apply False.elim assump_32


variable (p5 p2 p0 p3 p6 p4 p7 p1 : Prop)
theorem file20_23415 : ((((((p5 ∧ p5) ∨ (p1 ∨ True)) → ((p0 → False) ∧ (p5 ∧ p7))) ∧ (((p0 ∧ False) → (p4 ∧ p6)) ∧ ((p3 ∨ p0) → (True → p3)))) ∧ ((((True → p1) → False) ∨ ((p4 ∨ p4) → False)) ∧ (((False ∧ p2) → False) → False))) → False) := by
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
          case inl assump_16 =>
            have assump_44 : ((False ∧ p2) → False) := by
              intro assump_23
              cases assump_23
              case intro assump_24 assump_25 =>
                apply False.elim assump_24
            let assump_22 := assump_15 assump_44
            apply False.elim assump_22
          case inr assump_17 =>
            have assump_45 : ((False ∧ p2) → False) := by
              intro assump_36
              cases assump_36
              case intro assump_37 assump_38 =>
                apply False.elim assump_37
            let assump_35 := assump_15 assump_45
            apply False.elim assump_35


variable (p4 p2 p7 p5 p1 p6 p0 : Prop)
theorem file20_24630 : ((((((False → p2) → False) → ((p2 ∨ p5) ∧ (p6 ∨ p2))) → (((p4 ∨ p5) → False) → ((p7 → False) → (p2 → True)))) ∧ ((((p7 → True) ∨ (p1 ∧ p7)) → False) ∧ (((True ∨ False) ∨ (p0 → False)) ∨ ((p7 → p4) ∧ (p6 → False))))) → False) := by
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
          case inl assump_14 =>
            have assump_46 : ((p7 → True) ∨ (p1 ∧ p7)) := by
              apply Or.inl
              intro assump_19
              apply True.intro
            let assump_18 := assump_6 assump_46
            apply False.elim assump_18
          case inr assump_15 =>
            apply False.elim assump_15
        case inr assump_13 =>
          have assump_47 : ((p7 → True) ∨ (p1 ∧ p7)) := by
            apply Or.inl
            intro assump_29
            apply True.intro
          let assump_28 := assump_6 assump_47
          apply False.elim assump_28
      case inr assump_11 =>
        cases assump_11
        case intro assump_33 assump_34 =>
          have assump_48 : ((p7 → True) ∨ (p1 ∧ p7)) := by
            apply Or.inl
            intro assump_42
            apply True.intro
          let assump_41 := assump_6 assump_48
          apply False.elim assump_41


variable (p4 p5 p7 p6 p1 p0 : Prop)
theorem file20_26084 : (((((p5 → False) ∨ (p4 → p5)) ∧ ((p1 → False) → (True → p6))) ∧ (((False ∧ False) → False) → False)) → ((((p4 ∨ p0) → (p1 → False)) → False) → (((p1 → p1) ∧ (p0 ∧ p1)) ∨ ((p7 → False) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        apply Or.inr
        intro assump_20
        have assump_55 : ((False ∧ False) → False) := by
          intro assump_25
          cases assump_25
          case intro assump_26 assump_27 =>
            apply False.elim assump_26
        let assump_24 := assump_6 assump_55
        apply False.elim assump_24
      case inr assump_10 =>
        apply Or.inr
        intro assump_42
        have assump_56 : ((False ∧ False) → False) := by
          intro assump_47
          cases assump_47
          case intro assump_48 assump_49 =>
            apply False.elim assump_48
        let assump_46 := assump_6 assump_56
        apply False.elim assump_46


variable (p6 p1 p4 p0 p5 p3 p7 : Prop)
theorem file20_27197 : (((((p6 → False) ∨ (p1 → p3)) ∧ ((False ∧ p0) ∧ (p0 → False))) ∧ (((p5 ∧ p1) ∨ (p5 → p3)) ∧ ((p3 → False) ∨ (False → True)))) → ((((p6 ∨ p7) ∧ (p4 ∧ True)) ∨ ((p3 ∨ False) → (False → p4))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case inl assump_7 =>
        cases assump_6
        case intro assump_11 assump_12 =>
          cases assump_1
          case intro assump_17 assump_18 =>
            cases assump_17
            case intro assump_19 assump_20 =>
              cases assump_19
              case inl assump_21 =>
                cases assump_20
                case intro assump_25 assump_26 =>
                  cases assump_25
                  case intro assump_27 assump_28 =>
                    apply False.elim assump_27
              case inr assump_22 =>
                cases assump_20
                case intro assump_33 assump_34 =>
                  cases assump_33
                  case intro assump_35 assump_36 =>
                    apply False.elim assump_35
      case inr assump_8 =>
        cases assump_6
        case intro assump_41 assump_42 =>
          cases assump_1
          case intro assump_47 assump_48 =>
            cases assump_47
            case intro assump_49 assump_50 =>
              cases assump_49
              case inl assump_51 =>
                cases assump_50
                case intro assump_55 assump_56 =>
                  cases assump_55
                  case intro assump_57 assump_58 =>
                    apply False.elim assump_57
              case inr assump_52 =>
                cases assump_50
                case intro assump_63 assump_64 =>
                  cases assump_63
                  case intro assump_65 assump_66 =>
                    apply False.elim assump_65
  case inr assump_4 =>
    cases assump_1
    case intro assump_71 assump_72 =>
      cases assump_71
      case intro assump_73 assump_74 =>
        cases assump_73
        case inl assump_75 =>
          cases assump_74
          case intro assump_79 assump_80 =>
            cases assump_79
            case intro assump_81 assump_82 =>
              apply False.elim assump_81
        case inr assump_76 =>
          cases assump_74
          case intro assump_87 assump_88 =>
            cases assump_87
            case intro assump_89 assump_90 =>
              apply False.elim assump_89


variable (p0 p3 p2 p4 p7 p5 : Prop)
theorem file20_29742 : (((((p2 → False) → False) ∧ ((p5 → False) → False)) ∧ (((p3 → p2) → False) ∧ ((p7 → False) ∧ (True ∧ p7)))) → ((((p3 ∧ p0) ∨ (False → p3)) → False) ∨ (((p0 → False) ∧ (p4 → False)) → ((p2 → p0) ∧ (p0 ∧ p3))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          cases assump_15
          case intro assump_18 assump_19 =>
            apply Or.inl
            intro assump_24
            cases assump_24
            case inl assump_25 =>
              cases assump_25
              case intro assump_27 assump_28 =>
                have assump_48 : p7 := by
                  exact assump_19
                let assump_36 := assump_14 assump_48
                apply False.elim assump_36
            case inr assump_26 =>
              have assump_49 : p7 := by
                exact assump_19
              let assump_44 := assump_14 assump_49
              apply False.elim assump_44


variable (p5 p2 p3 : Prop)
theorem file20_30892 : ((((((p5 ∧ p5) ∨ (p3 → False)) ∧ ((p2 → False) ∧ (p3 ∧ p2))) → False) → False) → False) := by
  intro assump_1
  have assump_53 : ((((p5 ∧ p5) ∨ (p3 → False)) ∧ ((p2 → False) ∧ (p3 ∧ p2))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_7
          case intro assump_16 assump_17 =>
            cases assump_17
            case intro assump_20 assump_21 =>
              have assump_54 : p2 := by
                exact assump_21
              let assump_28 := assump_16 assump_54
              apply False.elim assump_28
      case inr assump_9 =>
        cases assump_7
        case intro assump_34 assump_35 =>
          cases assump_35
          case intro assump_38 assump_39 =>
            have assump_55 : p2 := by
              exact assump_39
            let assump_46 := assump_34 assump_55
            apply False.elim assump_46
  let assump_4 := assump_1 assump_53
  apply False.elim assump_4


variable (p1 p5 p2 p4 p6 p3 p0 : Prop)
theorem file20_32036 : ((((((p3 ∧ False) ∨ (p6 → False)) ∧ ((p1 ∧ p5) → False)) ∧ (((p0 → False) → False) ∧ ((p0 → False) ∨ (p5 ∧ p3)))) ∧ ((((False → p4) → False) → ((p2 → True) → False)) → False)) → False) := by
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
          case intro assump_10 assump_11 =>
            apply False.elim assump_11
        case inr assump_9 =>
          cases assump_5
          case intro assump_20 assump_21 =>
            cases assump_21
            case inl assump_24 =>
              have assump_72 : (((False → p4) → False) → ((p2 → True) → False)) := by
                intro assump_31
                intro assump_32
                have assump_73 : (False → p4) := by
                  intro assump_38
                  apply False.elim assump_38
                let assump_37 := assump_31 assump_73
                apply False.elim assump_37
              let assump_30 := assump_3 assump_72
              apply False.elim assump_30
            case inr assump_25 =>
              cases assump_25
              case intro assump_47 assump_48 =>
                have assump_74 : (((False → p4) → False) → ((p2 → True) → False)) := by
                  intro assump_56
                  intro assump_57
                  have assump_75 : (False → p4) := by
                    intro assump_63
                    apply False.elim assump_63
                  let assump_62 := assump_56 assump_75
                  apply False.elim assump_62
                let assump_55 := assump_3 assump_74
                apply False.elim assump_55


variable (p2 p6 p3 p0 p4 p1 : Prop)
theorem file20_33857 : ((((((p0 ∨ p3) → (p6 → p2)) → False) ∧ (((p6 → False) ∨ (p0 → p4)) ∧ ((p0 ∨ p6) ∨ (p0 → False)))) ∧ ((((p4 → False) ∨ (p6 → False)) → ((False ∨ p1) → (p4 → p4))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_9
          case inl assump_14 =>
            cases assump_14
            case inl assump_16 =>
              have assump_174 : (((p4 → False) ∨ (p6 → False)) → ((False ∨ p1) → (p4 → p4))) := by
                intro assump_23
                intro assump_24
                intro assump_25
                cases assump_24
                case inl assump_28 =>
                  apply False.elim assump_28
                case inr assump_29 =>
                  cases assump_23
                  case inl assump_34 =>
                    exact assump_25
                  case inr assump_35 =>
                    exact assump_25
              let assump_22 := assump_3 assump_174
              apply False.elim assump_22
            case inr assump_17 =>
              have assump_175 : (((p4 → False) ∨ (p6 → False)) → ((False ∨ p1) → (p4 → p4))) := by
                intro assump_48
                intro assump_49
                intro assump_50
                cases assump_49
                case inl assump_53 =>
                  apply False.elim assump_53
                case inr assump_54 =>
                  cases assump_48
                  case inl assump_59 =>
                    exact assump_50
                  case inr assump_60 =>
                    exact assump_50
              let assump_47 := assump_3 assump_175
              apply False.elim assump_47
          case inr assump_15 =>
            have assump_176 : (((p4 → False) ∨ (p6 → False)) → ((False ∨ p1) → (p4 → p4))) := by
              intro assump_73
              intro assump_74
              intro assump_75
              cases assump_74
              case inl assump_78 =>
                apply False.elim assump_78
              case inr assump_79 =>
                cases assump_73
                case inl assump_84 =>
                  exact assump_75
                case inr assump_85 =>
                  exact assump_75
            let assump_72 := assump_3 assump_176
            apply False.elim assump_72
        case inr assump_11 =>
          cases assump_9
          case inl assump_95 =>
            cases assump_95
            case inl assump_97 =>
              have assump_177 : (((p4 → False) ∨ (p6 → False)) → ((False ∨ p1) → (p4 → p4))) := by
                intro assump_104
                intro assump_105
                intro assump_106
                cases assump_105
                case inl assump_109 =>
                  apply False.elim assump_109
                case inr assump_110 =>
                  cases assump_104
                  case inl assump_115 =>
                    exact assump_106
                  case inr assump_116 =>
                    exact assump_106
              let assump_103 := assump_3 assump_177
              apply False.elim assump_103
            case inr assump_98 =>
              have assump_178 : (((p4 → False) ∨ (p6 → False)) → ((False ∨ p1) → (p4 → p4))) := by
                intro assump_129
                intro assump_130
                intro assump_131
                cases assump_130
                case inl assump_134 =>
                  apply False.elim assump_134
                case inr assump_135 =>
                  cases assump_129
                  case inl assump_140 =>
                    exact assump_131
                  case inr assump_141 =>
                    exact assump_131
              let assump_128 := assump_3 assump_178
              apply False.elim assump_128
          case inr assump_96 =>
            have assump_179 : (((p4 → False) ∨ (p6 → False)) → ((False ∨ p1) → (p4 → p4))) := by
              intro assump_154
              intro assump_155
              intro assump_156
              cases assump_155
              case inl assump_159 =>
                apply False.elim assump_159
              case inr assump_160 =>
                cases assump_154
                case inl assump_165 =>
                  exact assump_156
                case inr assump_166 =>
                  exact assump_156
            let assump_153 := assump_3 assump_179
            apply False.elim assump_153


variable (p7 p5 p3 p1 p2 p4 : Prop)
theorem file20_38477 : (((((False ∨ p2) → False) ∧ ((p1 → True) → False)) → False) → ((((p5 ∨ True) ∨ (p7 → p3)) ∨ ((True ∧ p5) → False)) ∨ (((p4 ∧ p5) ∨ (False → False)) → ((p3 → False) → (p3 → p5))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inr
  apply True.intro


variable (p1 p3 p2 p4 p6 p7 p5 : Prop)
theorem file20_38822 : ((((((p3 ∧ p6) ∨ (False → False)) ∧ ((p3 ∨ p7) → False)) → (((True ∨ p6) ∨ (p4 ∧ False)) ∧ ((p5 → True) ∨ (p1 ∧ p7)))) → ((((p3 → False) ∧ (p4 ∧ p2)) → ((p5 ∧ False) → False)) → False)) → False) := by
  intro assump_1
  have assump_52 : ((((p3 ∧ p6) ∨ (False → False)) ∧ ((p3 ∨ p7) → False)) → (((True ∨ p6) ∨ (p4 ∧ False)) ∧ ((p5 → True) ∨ (p1 ∧ p7)))) := by
    intro assump_5
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply Or.inl
          apply Or.inl
          apply True.intro
      case inr assump_9 =>
        apply Or.inl
        apply Or.inl
        apply True.intro
    cases assump_5
    case intro assump_22 assump_23 =>
      cases assump_22
      case inl assump_24 =>
        cases assump_24
        case intro assump_26 assump_27 =>
          apply Or.inl
          intro assump_34
          apply True.intro
      case inr assump_25 =>
        apply Or.inl
        intro assump_39
        apply True.intro
  let assump_4 := assump_1 assump_52
  have assump_53 : (((p3 → False) ∧ (p4 ∧ p2)) → ((p5 ∧ False) → False)) := by
    intro assump_41
    intro assump_42
    cases assump_42
    case intro assump_43 assump_44 =>
      apply False.elim assump_44
  let assump_40 := assump_4 assump_53
  apply False.elim assump_40


variable (p3 p0 p2 p4 : Prop)
theorem file20_40271 : ((((((p4 ∨ p0) → (p2 → True)) ∨ ((True → False) → False)) → (((False ∨ p0) ∨ (p3 → True)) ∨ ((p4 ∨ False) → False))) → False) → False) := by
  intro assump_1
  have assump_17 : ((((p4 ∨ p0) → (p2 → True)) ∨ ((True → False) → False)) → (((False ∨ p0) ∨ (p3 → True)) ∨ ((p4 ∨ False) → False))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inl
      apply Or.inr
      intro assump_10
      apply True.intro
    case inr assump_7 =>
      apply Or.inl
      apply Or.inr
      intro assump_13
      apply True.intro
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p2 p1 p4 p0 p5 p3 p7 : Prop)
theorem file20_40951 : (((((p7 ∨ True) ∨ (p1 → p4)) → False) → False) ∨ ((((p4 ∧ p1) ∧ (True → p5)) → ((p1 ∧ p3) ∨ (p5 ∨ p5))) → (((p5 → p0) → (p2 ∧ p3)) ∧ ((p4 → p5) → False)))) := by
  apply Or.inl
  intro assump_1
  have assump_8 : ((p7 ∨ True) ∨ (p1 → p4)) := by
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p3 p6 : Prop)
theorem file20_41362 : ((((((True → False) → (p3 → p6)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_25 : ((((True → False) → (p3 → p6)) → False) → False) := by
    intro assump_5
    have assump_26 : ((True → False) → (p3 → p6)) := by
      intro assump_9
      intro assump_10
      have assump_27 : True := by
        apply True.intro
      let assump_15 := assump_9 assump_27
      apply False.elim assump_15
    let assump_8 := assump_5 assump_26
    apply False.elim assump_8
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p2 p1 p0 p3 p4 p6 : Prop)
theorem file20_41974 : (((((p0 → True) → False) ∨ ((False ∨ p0) → False)) → (((True → False) → (p0 ∨ p4)) ∨ ((p1 ∨ p2) → False))) ∨ ((((p6 → p3) → False) → ((p6 → False) → False)) ∨ (((p1 ∧ p1) → (p2 ∧ p6)) → ((p2 → p3) ∧ (p4 ∨ p6))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    have assump_22 : True := by
      apply True.intro
    let assump_9 := assump_6 assump_22
    apply False.elim assump_9
  case inr assump_3 =>
    apply Or.inl
    intro assump_15
    have assump_23 : True := by
      apply True.intro
    let assump_18 := assump_15 assump_23
    apply False.elim assump_18


variable (p3 p7 p1 p2 p0 p6 : Prop)
theorem file20_42672 : (((((False → False) → False) ∨ ((False ∧ p1) ∧ (True ∧ p7))) → (((p2 ∨ p0) → False) → ((p7 → False) → (p3 → False)))) ∨ ((((True → p6) ∨ (p0 ∨ p2)) ∧ ((True → False) ∧ (True → False))) → (((p7 → False) → False) ∨ ((p3 → False) → False)))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_1
  case inl assump_11 =>
    have assump_28 : (False → False) := by
      intro assump_16
      apply False.elim assump_16
    let assump_15 := assump_11 assump_28
    apply False.elim assump_15
  case inr assump_12 =>
    cases assump_12
    case intro assump_22 assump_23 =>
      cases assump_22
      case intro assump_24 assump_25 =>
        apply False.elim assump_24


variable (p2 p7 p6 p3 : Prop)
theorem file20_43444 : (((((p7 ∨ p3) ∧ (True ∨ False)) → ((p2 ∨ p6) → (p7 → p7))) → False) → False) := by
  intro assump_1
  have assump_59 : (((p7 ∨ p3) ∧ (True ∨ False)) → ((p2 ∨ p6) → (p7 → p7))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case inl assump_10 =>
      cases assump_5
      case intro assump_14 assump_15 =>
        cases assump_14
        case inl assump_16 =>
          cases assump_15
          case inl assump_20 =>
            exact assump_16
          case inr assump_21 =>
            apply False.elim assump_21
        case inr assump_17 =>
          cases assump_15
          case inl assump_28 =>
            exact assump_7
          case inr assump_29 =>
            apply False.elim assump_29
    case inr assump_11 =>
      cases assump_5
      case intro assump_36 assump_37 =>
        cases assump_36
        case inl assump_38 =>
          cases assump_37
          case inl assump_42 =>
            exact assump_38
          case inr assump_43 =>
            apply False.elim assump_43
        case inr assump_39 =>
          cases assump_37
          case inl assump_50 =>
            exact assump_7
          case inr assump_51 =>
            apply False.elim assump_51
  let assump_4 := assump_1 assump_59
  apply False.elim assump_4


variable (p5 p3 p7 p1 p0 p2 : Prop)
theorem file20_44795 : ((((((p7 ∧ p5) → (False → False)) → False) → (((p1 → False) ∨ (p7 ∧ p3)) ∧ ((p0 → False) ∨ (p2 → p0)))) → False) → False) := by
  intro assump_1
  have assump_37 : ((((p7 ∧ p5) → (False → False)) → False) → (((p1 → False) ∨ (p7 ∧ p3)) ∧ ((p0 → False) ∨ (p2 → p0)))) := by
    intro assump_5
    apply And.intro
    apply Or.inl
    intro assump_8
    have assump_38 : ((p7 ∧ p5) → (False → False)) := by
      intro assump_13
      intro assump_14
      apply False.elim assump_14
    let assump_12 := assump_5 assump_38
    apply False.elim assump_12
    apply Or.inl
    intro assump_22
    have assump_39 : ((p7 ∧ p5) → (False → False)) := by
      intro assump_27
      intro assump_28
      apply False.elim assump_28
    let assump_26 := assump_5 assump_39
    apply False.elim assump_26
  let assump_4 := assump_1 assump_37
  apply False.elim assump_4


variable (p7 p4 p2 p1 p0 p5 p3 : Prop)
theorem file20_45717 : (((((p4 ∨ p4) ∨ (p5 ∧ p2)) ∨ ((p1 ∧ False) → False)) → False) → ((((p1 ∨ p7) → False) → False) ∨ (((p3 ∨ p2) → False) ∨ ((p0 → False) → False)))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_19 : (((p4 ∨ p4) ∨ (p5 ∧ p2)) ∨ ((p1 ∧ False) → False)) := by
    apply Or.inr
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      apply False.elim assump_11
  let assump_8 := assump_1 assump_19
  apply False.elim assump_8


variable (p7 p5 p4 p3 p2 : Prop)
theorem file20_46242 : ((((((p2 ∧ True) → (p4 ∨ p2)) → False) → False) ∧ ((((p7 ∧ p4) ∧ (True → False)) → ((p7 ∨ p2) ∨ (p3 ∨ p5))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_23 : (((p7 ∧ p4) ∧ (True → False)) → ((p7 ∨ p2) ∨ (p3 ∨ p5))) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          apply Or.inl
          apply Or.inl
          exact assump_12
    let assump_8 := assump_3 assump_23
    apply False.elim assump_8


variable (p4 p3 p1 p5 : Prop)
theorem file20_46870 : ((((((p5 ∧ p3) ∨ (p3 → False)) → ((False → False) → False)) → (((p4 → False) ∧ (p4 ∧ False)) → ((p4 ∧ True) → (p1 → False)))) → False) → False) := by
  intro assump_1
  have assump_30 : ((((p5 ∧ p3) ∨ (p3 → False)) → ((False → False) → False)) → (((p4 → False) ∧ (p4 ∧ False)) → ((p4 ∧ True) → (p1 → False)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    cases assump_7
    case intro assump_11 assump_12 =>
      cases assump_6
      case intro assump_17 assump_18 =>
        cases assump_18
        case intro assump_21 assump_22 =>
          apply False.elim assump_22
  let assump_4 := assump_1 assump_30
  apply False.elim assump_4


variable (p4 p5 p3 p7 p6 : Prop)
theorem file20_47605 : ((((((p3 → p3) → (p6 ∧ False)) → False) ∧ (((p5 ∨ p6) → (p4 → False)) → False)) ∧ ((((True ∨ p7) → False) → False) → False)) → False) := by
  intro assump_11
  cases assump_11
  case intro assump_12 assump_13 =>
    cases assump_12
    case intro assump_14 assump_15 =>
      have assump_33 : (((True ∨ p7) → False) → False) := by
        intro assump_23
        have assump_34 : (True ∨ p7) := by
          apply Or.inl
          apply True.intro
        let assump_26 := assump_23 assump_34
        apply False.elim assump_26
      let assump_22 := assump_13 assump_33
      apply False.elim assump_22


variable (p3 p1 p0 p5 p6 : Prop)
theorem file20_48266 : ((((((p0 ∨ False) ∧ (True ∨ p6)) ∨ ((p0 → False) ∧ (p3 ∨ p6))) → (((True ∨ p1) → False) → ((False ∨ p6) ∧ (p5 → False)))) → False) → False) := by
  intro assump_1
  have assump_103 : ((((p0 ∨ False) ∧ (True ∨ p6)) ∨ ((p0 → False) ∧ (p3 ∨ p6))) → (((True ∨ p1) → False) → ((False ∨ p6) ∧ (p5 → False)))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    cases assump_5
    case inl assump_9 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_11
        case inl assump_13 =>
          cases assump_12
          case inl assump_17 =>
            have assump_104 : (True ∨ p1) := by
              apply Or.inl
              apply True.intro
            let assump_22 := assump_6 assump_104
            apply False.elim assump_22
          case inr assump_18 =>
            apply Or.inr
            exact assump_18
        case inr assump_14 =>
          apply False.elim assump_14
    case inr assump_10 =>
      cases assump_10
      case intro assump_30 assump_31 =>
        cases assump_31
        case inl assump_34 =>
          have assump_105 : (True ∨ p1) := by
            apply Or.inl
            apply True.intro
          let assump_40 := assump_6 assump_105
          apply False.elim assump_40
        case inr assump_35 =>
          apply Or.inr
          exact assump_35
    intro assump_46
    cases assump_5
    case inl assump_51 =>
      cases assump_51
      case intro assump_53 assump_54 =>
        cases assump_53
        case inl assump_55 =>
          cases assump_54
          case inl assump_59 =>
            have assump_106 : (True ∨ p1) := by
              apply Or.inl
              apply True.intro
            let assump_64 := assump_6 assump_106
            apply False.elim assump_64
          case inr assump_60 =>
            have assump_107 : (True ∨ p1) := by
              apply Or.inl
              apply True.intro
            let assump_72 := assump_6 assump_107
            apply False.elim assump_72
        case inr assump_56 =>
          apply False.elim assump_56
    case inr assump_52 =>
      cases assump_52
      case intro assump_78 assump_79 =>
        cases assump_79
        case inl assump_82 =>
          have assump_108 : (True ∨ p1) := by
            apply Or.inl
            apply True.intro
          let assump_88 := assump_6 assump_108
          apply False.elim assump_88
        case inr assump_83 =>
          have assump_109 : (True ∨ p1) := by
            apply Or.inl
            apply True.intro
          let assump_96 := assump_6 assump_109
          apply False.elim assump_96
  let assump_4 := assump_1 assump_103
  apply False.elim assump_4


variable (p2 p7 p4 p3 p0 p1 p5 : Prop)
theorem file20_50996 : (((((p1 ∨ p7) → (p0 ∨ True)) → ((p4 ∧ p7) → False)) ∧ (((p0 ∧ p1) ∧ (p1 → p1)) ∨ ((p2 → p0) ∧ (p0 ∧ p5)))) → ((((p0 ∧ p7) ∧ (p0 ∨ p2)) → ((p5 → p5) ∨ (p2 → p3))) ∨ (((p1 ∨ p2) → (p0 → False)) → ((p0 → False) ∧ (True → False))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply Or.inl
          intro assump_18
          cases assump_18
          case intro assump_19 assump_20 =>
            cases assump_19
            case intro assump_21 assump_22 =>
              cases assump_20
              case inl assump_27 =>
                apply Or.inl
                intro assump_31
                exact assump_31
              case inr assump_28 =>
                apply Or.inl
                intro assump_36
                exact assump_36
    case inr assump_7 =>
      cases assump_7
      case intro assump_39 assump_40 =>
        cases assump_40
        case intro assump_43 assump_44 =>
          apply Or.inl
          intro assump_49
          cases assump_49
          case intro assump_50 assump_51 =>
            cases assump_50
            case intro assump_52 assump_53 =>
              cases assump_51
              case inl assump_58 =>
                apply Or.inl
                intro assump_62
                exact assump_62
              case inr assump_59 =>
                apply Or.inl
                intro assump_67
                exact assump_67


variable (p4 p6 p5 p0 p2 p7 p1 : Prop)
theorem file20_52644 : (((((p2 → p2) → False) → ((p6 ∨ p1) → False)) → False) → ((((p4 ∨ p4) ∧ (False ∧ p6)) ∧ ((p2 ∨ p6) ∨ (p1 → p5))) → (((p0 → False) ∧ (p7 → p4)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_2
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


variable (p4 p0 p3 p7 : Prop)
theorem file20_53381 : (((((p7 ∧ False) ∨ (p0 ∧ p4)) → False) ∧ (((p3 ∧ True) ∨ (True ∨ True)) → False)) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    have assump_16 : ((p3 ∧ True) ∨ (True ∨ True)) := by
      apply Or.inr
      apply Or.inl
      apply True.intro
    let assump_12 := assump_7 assump_16
    apply False.elim assump_12


variable (p4 p5 p1 : Prop)
theorem file20_53786 : (((((True → False) ∨ (p4 ∧ p5)) → ((True ∧ p4) → (p1 → p4))) → False) → False) := by
  intro assump_12
  have assump_40 : (((True → False) ∨ (p4 ∧ p5)) → ((True ∧ p4) → (p1 → p4))) := by
    intro assump_16
    intro assump_17
    intro assump_18
    cases assump_17
    case intro assump_21 assump_22 =>
      cases assump_16
      case inl assump_27 =>
        exact assump_22
      case inr assump_28 =>
        cases assump_28
        case intro assump_31 assump_32 =>
          exact assump_31
  let assump_15 := assump_12 assump_40
  apply False.elim assump_15


variable (p2 p5 p0 p7 p4 p1 p3 : Prop)
theorem file20_54416 : (((((p4 ∨ False) → False) → False) → (((p0 → p0) ∨ (p3 ∨ p0)) ∧ ((p7 → True) → False))) → ((((p3 ∧ False) ∧ (p1 ∧ p4)) → False) ∨ (((p5 ∧ p7) ∧ (p2 → False)) ∨ ((p3 ∨ p1) → False)))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      apply False.elim assump_8


variable (p6 p7 p3 p5 p0 : Prop)
theorem file20_54849 : ((((((p7 ∨ p5) → False) ∨ ((p0 ∧ p3) → (p7 → True))) → (((False ∧ True) ∧ (p0 ∧ p6)) → False)) → False) → False) := by
  intro assump_22
  have assump_37 : ((((p7 ∨ p5) → False) ∨ ((p0 ∧ p3) → (p7 → True))) → (((False ∧ True) ∧ (p0 ∧ p6)) → False)) := by
    intro assump_26
    intro assump_27
    cases assump_27
    case intro assump_28 assump_29 =>
      cases assump_28
      case intro assump_30 assump_31 =>
        apply False.elim assump_30
  let assump_25 := assump_22 assump_37
  apply False.elim assump_25


variable (p1 p6 p5 p7 p4 p2 p3 : Prop)
theorem file20_55430 : ((((((p7 → p2) → (p1 ∧ False)) ∨ ((p2 ∧ p4) ∧ (p5 → True))) → (((p6 ∧ p3) → False) → ((False → False) ∧ (False → False)))) → False) → False) := by
  intro assump_1
  have assump_16 : ((((p7 → p2) → (p1 ∧ False)) ∨ ((p2 ∧ p4) ∧ (p5 → True))) → (((p6 ∧ p3) → False) → ((False → False) ∧ (False → False)))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    intro assump_7
    apply False.elim assump_7
    intro assump_10
    apply False.elim assump_10
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p1 p2 p0 p3 p4 : Prop)
theorem file20_56020 : ((((((p1 → p3) → False) → ((p0 → False) → (p2 ∨ p0))) → (((p1 ∨ p0) → False) → ((p4 ∨ p3) → False))) ∧ ((((True ∨ p2) → (True → False)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_20 : (((True ∨ p2) → (True → False)) → False) := by
      intro assump_9
      have assump_21 : (True ∨ p2) := by
        apply Or.inl
        apply True.intro
      let assump_12 := assump_9 assump_21
      have assump_22 : True := by
        apply True.intro
      let assump_13 := assump_12 assump_22
      apply False.elim assump_13
    let assump_8 := assump_3 assump_20
    apply False.elim assump_8


variable (p3 p6 p2 p5 p0 p1 p7 p4 : Prop)
theorem file20_56746 : ((((((p1 ∧ p7) ∧ (p5 → False)) ∧ ((p2 ∧ p6) ∧ (True ∨ p0))) → False) ∧ ((((p7 ∨ p0) ∨ (True ∧ p5)) ∨ ((p1 ∨ p1) ∧ (p3 → p7))) ∧ (((p4 → p4) → False) ∧ ((p0 → True) ∧ (p0 ∧ p4))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_10
          case inl assump_12 =>
            cases assump_7
            case intro assump_16 assump_17 =>
              cases assump_17
              case intro assump_20 assump_21 =>
                cases assump_21
                case intro assump_24 assump_25 =>
                  have assump_161 : (p4 → p4) := by
                    intro assump_35
                    exact assump_35
                  let assump_34 := assump_16 assump_161
                  apply False.elim assump_34
          case inr assump_13 =>
            cases assump_7
            case intro assump_43 assump_44 =>
              cases assump_44
              case intro assump_47 assump_48 =>
                cases assump_48
                case intro assump_51 assump_52 =>
                  have assump_162 : (p4 → p4) := by
                    intro assump_62
                    exact assump_62
                  let assump_61 := assump_43 assump_162
                  apply False.elim assump_61
        case inr assump_11 =>
          cases assump_11
          case intro assump_68 assump_69 =>
            cases assump_7
            case intro assump_74 assump_75 =>
              cases assump_75
              case intro assump_78 assump_79 =>
                cases assump_79
                case intro assump_82 assump_83 =>
                  have assump_163 : (p4 → p4) := by
                    intro assump_93
                    exact assump_93
                  let assump_92 := assump_74 assump_163
                  apply False.elim assump_92
      case inr assump_9 =>
        cases assump_9
        case intro assump_99 assump_100 =>
          cases assump_99
          case inl assump_101 =>
            cases assump_7
            case intro assump_107 assump_108 =>
              cases assump_108
              case intro assump_111 assump_112 =>
                cases assump_112
                case intro assump_115 assump_116 =>
                  have assump_164 : (p4 → p4) := by
                    intro assump_126
                    exact assump_126
                  let assump_125 := assump_107 assump_164
                  apply False.elim assump_125
          case inr assump_102 =>
            cases assump_7
            case intro assump_136 assump_137 =>
              cases assump_137
              case intro assump_140 assump_141 =>
                cases assump_141
                case intro assump_144 assump_145 =>
                  have assump_165 : (p4 → p4) := by
                    intro assump_155
                    exact assump_155
                  let assump_154 := assump_136 assump_165
                  apply False.elim assump_154


variable (p1 p2 p4 p7 p0 p3 p5 p6 : Prop)
theorem file20_59922 : ((((((False ∧ p3) ∧ (p6 ∧ True)) ∨ ((p4 ∧ True) → False)) ∧ (((p0 ∨ p4) ∧ (p1 ∨ p3)) ∨ ((p1 ∧ p6) → False))) ∧ ((((p6 → p7) ∨ (p4 ∧ p1)) → ((p2 → False) → (p7 → p5))) ∧ (((p0 ∨ False) ∧ (True → False)) ∧ ((p5 ∨ p3) ∨ (p5 ∧ p7))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_8
          case intro assump_10 assump_11 =>
            apply False.elim assump_10
      case inr assump_7 =>
        cases assump_5
        case inl assump_16 =>
          cases assump_16
          case intro assump_18 assump_19 =>
            cases assump_18
            case inl assump_20 =>
              cases assump_19
              case inl assump_24 =>
                cases assump_3
                case intro assump_28 assump_29 =>
                  cases assump_29
                  case intro assump_32 assump_33 =>
                    cases assump_32
                    case intro assump_34 assump_35 =>
                      cases assump_34
                      case inl assump_36 =>
                        cases assump_33
                        case inl assump_42 =>
                          cases assump_42
                          case inl assump_44 =>
                            have assump_270 : True := by
                              apply True.intro
                            let assump_49 := assump_35 assump_270
                            apply False.elim assump_49
                          case inr assump_45 =>
                            have assump_271 : True := by
                              apply True.intro
                            let assump_56 := assump_35 assump_271
                            apply False.elim assump_56
                        case inr assump_43 =>
                          cases assump_43
                          case intro assump_60 assump_61 =>
                            have assump_272 : True := by
                              apply True.intro
                            let assump_68 := assump_35 assump_272
                            apply False.elim assump_68
                      case inr assump_37 =>
                        apply False.elim assump_37
              case inr assump_25 =>
                cases assump_3
                case intro assump_76 assump_77 =>
                  cases assump_77
                  case intro assump_80 assump_81 =>
                    cases assump_80
                    case intro assump_82 assump_83 =>
                      cases assump_82
                      case inl assump_84 =>
                        cases assump_81
                        case inl assump_90 =>
                          cases assump_90
                          case inl assump_92 =>
                            have assump_273 : True := by
                              apply True.intro
                            let assump_97 := assump_83 assump_273
                            apply False.elim assump_97
                          case inr assump_93 =>
                            have assump_274 : True := by
                              apply True.intro
                            let assump_104 := assump_83 assump_274
                            apply False.elim assump_104
                        case inr assump_91 =>
                          cases assump_91
                          case intro assump_108 assump_109 =>
                            have assump_275 : True := by
                              apply True.intro
                            let assump_116 := assump_83 assump_275
                            apply False.elim assump_116
                      case inr assump_85 =>
                        apply False.elim assump_85
            case inr assump_21 =>
              cases assump_19
              case inl assump_124 =>
                cases assump_3
                case intro assump_128 assump_129 =>
                  cases assump_129
                  case intro assump_132 assump_133 =>
                    cases assump_132
                    case intro assump_134 assump_135 =>
                      cases assump_134
                      case inl assump_136 =>
                        cases assump_133
                        case inl assump_142 =>
                          cases assump_142
                          case inl assump_144 =>
                            have assump_276 : True := by
                              apply True.intro
                            let assump_149 := assump_135 assump_276
                            apply False.elim assump_149
                          case inr assump_145 =>
                            have assump_277 : True := by
                              apply True.intro
                            let assump_156 := assump_135 assump_277
                            apply False.elim assump_156
                        case inr assump_143 =>
                          cases assump_143
                          case intro assump_160 assump_161 =>
                            have assump_278 : True := by
                              apply True.intro
                            let assump_168 := assump_135 assump_278
                            apply False.elim assump_168
                      case inr assump_137 =>
                        apply False.elim assump_137
              case inr assump_125 =>
                cases assump_3
                case intro assump_176 assump_177 =>
                  cases assump_177
                  case intro assump_180 assump_181 =>
                    cases assump_180
                    case intro assump_182 assump_183 =>
                      cases assump_182
                      case inl assump_184 =>
                        cases assump_181
                        case inl assump_190 =>
                          cases assump_190
                          case inl assump_192 =>
                            have assump_279 : True := by
                              apply True.intro
                            let assump_197 := assump_183 assump_279
                            apply False.elim assump_197
                          case inr assump_193 =>
                            have assump_280 : True := by
                              apply True.intro
                            let assump_204 := assump_183 assump_280
                            apply False.elim assump_204
                        case inr assump_191 =>
                          cases assump_191
                          case intro assump_208 assump_209 =>
                            have assump_281 : True := by
                              apply True.intro
                            let assump_216 := assump_183 assump_281
                            apply False.elim assump_216
                      case inr assump_185 =>
                        apply False.elim assump_185
        case inr assump_17 =>
          cases assump_3
          case intro assump_224 assump_225 =>
            cases assump_225
            case intro assump_228 assump_229 =>
              cases assump_228
              case intro assump_230 assump_231 =>
                cases assump_230
                case inl assump_232 =>
                  cases assump_229
                  case inl assump_238 =>
                    cases assump_238
                    case inl assump_240 =>
                      have assump_282 : True := by
                        apply True.intro
                      let assump_245 := assump_231 assump_282
                      apply False.elim assump_245
                    case inr assump_241 =>
                      have assump_283 : True := by
                        apply True.intro
                      let assump_252 := assump_231 assump_283
                      apply False.elim assump_252
                  case inr assump_239 =>
                    cases assump_239
                    case intro assump_256 assump_257 =>
                      have assump_284 : True := by
                        apply True.intro
                      let assump_264 := assump_231 assump_284
                      apply False.elim assump_264
                case inr assump_233 =>
                  apply False.elim assump_233


variable (p0 p1 p7 p2 p5 p3 p4 p6 : Prop)
theorem file20_68379 : (((((p6 → False) ∨ (p7 ∧ p0)) → ((p7 ∧ p6) ∨ (p6 ∧ p1))) ∧ (((p3 ∨ True) ∧ (p4 ∨ True)) → ((p2 ∧ False) ∧ (p6 ∧ p1)))) → ((((p4 → False) ∧ (p7 ∧ p0)) → ((p2 ∨ p3) → (False ∧ p3))) → (((False → False) ∨ (False → p5)) ∨ ((p7 → False) ∨ (p3 → False))))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    apply Or.inl
    apply Or.inl
    intro assump_11
    apply False.elim assump_11


variable (p1 p4 p2 p3 : Prop)
theorem file20_68860 : (((((p2 ∧ True) → False) ∧ ((True ∨ p3) → False)) → False) ∨ ((((False → False) → (True → False)) → False) → (((False → False) ∧ (p3 ∧ p3)) → ((p2 → p4) → (p1 ∧ p3))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_12 : (True ∨ p3) := by
      apply Or.inl
      apply True.intro
    let assump_8 := assump_3 assump_12
    apply False.elim assump_8


variable (p4 p7 p0 p6 p2 : Prop)
theorem file20_69325 : ((((((p0 → p2) → False) ∧ ((p7 ∨ p6) → False)) → (((p7 → False) → False) → ((p2 → True) ∨ (p4 → p2)))) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p0 → p2) → False) ∧ ((p7 ∨ p6) → False)) → (((p7 → False) → False) → ((p2 → True) ∨ (p4 → p2)))) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      apply Or.inl
      intro assump_15
      apply True.intro
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p6 p1 p5 p2 p0 p4 p7 : Prop)
theorem file20_69881 : (((((p4 → p4) ∧ (p7 ∧ p0)) ∧ ((p1 ∨ p4) ∨ (False → p1))) ∨ (((True ∨ p2) → False) → False)) ∨ ((((p1 ∨ False) ∨ (p5 ∨ p5)) ∧ ((p5 → p7) → (p6 ∨ p5))) ∧ (((p7 ∧ p1) ∨ (True → False)) ∧ ((p5 ∧ p1) → False)))) := by
  apply Or.inl
  apply Or.inr
  intro assump_35
  have assump_42 : (True ∨ p2) := by
    apply Or.inl
    apply True.intro
  let assump_38 := assump_35 assump_42
  apply False.elim assump_38


variable (p7 p5 p3 p1 p6 : Prop)
theorem file20_70342 : (((((p7 → False) ∧ (p1 → False)) ∧ ((p1 ∨ True) → False)) → False) ∨ ((((False → False) → False) ∨ ((p3 ∧ p5) ∧ (p3 → False))) → (((p6 ∧ False) → False) ∧ ((p1 ∨ False) → False)))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_16 : (p1 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_12 := assump_3 assump_16
      apply False.elim assump_12


variable (p4 p3 p5 : Prop)
theorem file20_70880 : (((((False ∨ p5) ∧ (p3 → p4)) → False) ∧ (((p3 ∨ True) ∨ (p5 → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_12 : ((p3 ∨ True) ∨ (p5 → False)) := by
      apply Or.inl
      apply Or.inr
      apply True.intro
    let assump_8 := assump_3 assump_12
    apply False.elim assump_8


variable (p7 p2 p4 p3 p0 p1 : Prop)
theorem file20_71290 : ((((((p0 → p0) → (False → p7)) ∧ ((True → False) → False)) → (((p1 ∨ True) ∨ (p2 → p4)) ∧ ((False → False) ∨ (p3 → False)))) → False) → False) := by
  intro assump_1
  have assump_24 : ((((p0 → p0) → (False → p7)) ∧ ((True → False) → False)) → (((p1 ∨ True) ∨ (p2 → p4)) ∧ ((False → False) ∨ (p3 → False)))) := by
    intro assump_5
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inl
      apply Or.inr
      apply True.intro
    cases assump_5
    case intro assump_12 assump_13 =>
      apply Or.inl
      intro assump_18
      apply False.elim assump_18
  let assump_4 := assump_1 assump_24
  apply False.elim assump_4


variable (p2 p0 p5 p7 p4 : Prop)
theorem file20_72012 : ((((((p4 ∧ p2) ∧ (p2 → False)) ∧ ((p5 ∧ p7) ∧ (p0 ∧ p2))) → False) → False) → False) := by
  intro assump_1
  have assump_43 : ((((p4 ∧ p2) ∧ (p2 → False)) ∧ ((p5 ∧ p7) ∧ (p0 ∧ p2))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_7
          case intro assump_18 assump_19 =>
            cases assump_18
            case intro assump_20 assump_21 =>
              cases assump_19
              case intro assump_26 assump_27 =>
                have assump_44 : p2 := by
                  exact assump_27
                let assump_36 := assump_9 assump_44
                apply False.elim assump_36
  let assump_4 := assump_1 assump_43
  apply False.elim assump_4


variable (p7 p0 p2 p6 p4 p3 p1 : Prop)
theorem file20_72928 : ((((((p0 ∧ p2) → False) ∧ ((p2 → False) ∨ (p3 → False))) → (((p4 ∨ p6) ∧ (p3 ∨ p2)) ∧ ((False → p0) ∨ (p0 → p2)))) ∧ ((((p4 ∧ p1) ∧ (p0 → False)) ∧ ((False ∨ p1) → (p3 ∨ p1))) ∧ (((False → p7) → False) ∧ ((p1 ∨ True) → (p1 → False))))) → False) := by
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
          case intro assump_12 assump_13 =>
            cases assump_7
            case intro assump_22 assump_23 =>
              have assump_33 : (p1 ∨ True) := by
                apply Or.inl
                exact assump_13
              let assump_28 := assump_23 assump_33
              have assump_34 : p1 := by
                exact assump_13
              let assump_29 := assump_28 assump_34
              apply False.elim assump_29


variable (p2 p5 p3 p4 : Prop)
theorem file20_73948 : (((((True → False) ∧ (True → False)) → ((p3 ∧ False) ∨ (p2 ∧ p3))) → False) → ((((p4 ∨ True) → False) → ((p3 ∨ p5) ∨ (False ∨ p3))) → False)) := by
  intro assump_1
  intro assump_2
  have assump_22 : (((True → False) ∧ (True → False)) → ((p3 ∧ False) ∨ (p2 ∧ p3))) := by
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      have assump_23 : True := by
        apply True.intro
      let assump_15 := assump_10 assump_23
      apply False.elim assump_15
  let assump_7 := assump_1 assump_22
  apply False.elim assump_7


variable (p3 p0 p4 p2 p6 : Prop)
theorem file20_74552 : ((((((p4 ∧ p2) ∧ (False ∧ p3)) ∧ ((p2 ∨ p0) ∨ (p2 → False))) → (((p6 ∧ p6) ∨ (p2 → True)) ∧ ((p4 → False) ∧ (True ∨ False)))) → False) → False) := by
  intro assump_7
  have assump_60 : ((((p4 ∧ p2) ∧ (False ∧ p3)) ∧ ((p2 ∨ p0) ∨ (p2 → False))) → (((p6 ∧ p6) ∨ (p2 → True)) ∧ ((p4 → False) ∧ (True ∨ False)))) := by
    intro assump_11
    apply And.intro
    cases assump_11
    case intro assump_12 assump_13 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          cases assump_15
          case intro assump_22 assump_23 =>
            apply False.elim assump_22
    apply And.intro
    intro assump_26
    cases assump_11
    case intro assump_29 assump_30 =>
      cases assump_29
      case intro assump_31 assump_32 =>
        cases assump_31
        case intro assump_33 assump_34 =>
          cases assump_32
          case intro assump_39 assump_40 =>
            apply False.elim assump_39
    cases assump_11
    case intro assump_43 assump_44 =>
      cases assump_43
      case intro assump_45 assump_46 =>
        cases assump_45
        case intro assump_47 assump_48 =>
          cases assump_46
          case intro assump_53 assump_54 =>
            apply False.elim assump_53
  let assump_10 := assump_7 assump_60
  apply False.elim assump_10


variable (p3 p7 p1 p4 : Prop)
theorem file20_75954 : ((((((p7 ∨ p1) → False) → ((p4 ∨ True) ∨ (True → False))) ∨ (((p4 ∧ p4) ∧ (p3 → False)) → False)) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p7 ∨ p1) → False) → ((p4 ∨ True) ∨ (True → False))) ∨ (((p4 ∧ p4) ∧ (p3 → False)) → False)) := by
    apply Or.inl
    intro assump_5
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p7 p3 p0 p6 p1 p5 p2 : Prop)
theorem file20_76433 : (((((p1 ∧ True) → False) ∧ ((p3 ∧ p1) ∧ (p2 ∨ p7))) → (((p5 → False) → (p3 → False)) ∨ ((True ∧ True) ∨ (p5 ∧ False)))) ∨ ((((p3 ∧ p0) ∨ (True → False)) ∨ ((p6 → p6) ∨ (p5 ∧ True))) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case inl assump_14 =>
          apply Or.inl
          intro assump_18
          intro assump_19
          have assump_50 : (p1 ∧ True) := by
            apply And.intro
            exact assump_9
            apply True.intro
          let assump_29 := assump_2 assump_50
          apply False.elim assump_29
        case inr assump_15 =>
          apply Or.inl
          intro assump_35
          intro assump_36
          have assump_51 : (p1 ∧ True) := by
            apply And.intro
            exact assump_9
            apply True.intro
          let assump_46 := assump_2 assump_51
          apply False.elim assump_46


variable (p0 p4 p6 p7 p5 p2 p1 : Prop)
theorem file20_77548 : (((((p4 ∨ p1) ∨ (p5 ∧ p4)) ∨ ((p6 → False) → (True ∨ p6))) ∨ (((False ∧ False) ∧ (p0 ∧ p1)) ∧ ((p5 ∧ True) → False))) ∧ ((((p6 ∨ False) → (p7 → p1)) → ((p0 → False) → False)) → (((p7 ∨ p1) ∨ (p2 → False)) → ((p1 ∨ True) ∨ (False ∧ p0))))) := by
  apply And.intro
  apply Or.inl
  apply Or.inr
  intro assump_1
  apply Or.inl
  apply True.intro
  intro assump_4
  intro assump_5
  cases assump_5
  case inl assump_6 =>
    cases assump_6
    case inl assump_8 =>
      apply Or.inl
      apply Or.inr
      apply True.intro
    case inr assump_9 =>
      apply Or.inl
      apply Or.inl
      exact assump_9
  case inr assump_7 =>
    apply Or.inl
    apply Or.inr
    apply True.intro


variable (p2 p7 p5 p0 p3 p4 p6 : Prop)
theorem file20_78296 : (((((p7 ∧ p0) ∧ (p3 → False)) → False) ∨ (((True → p4) ∨ (False → False)) ∨ ((p7 → p2) → False))) → ((((False ∧ p5) ∧ (p6 ∧ p2)) ∧ ((p0 ∧ p5) ∧ (p6 → False))) → (((p5 ∨ p6) → (p6 ∨ p6)) → ((p3 ∧ True) → (p0 ∧ p7))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  apply And.intro
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_2
    case intro assump_13 assump_14 =>
      cases assump_13
      case intro assump_15 assump_16 =>
        cases assump_15
        case intro assump_17 assump_18 =>
          apply False.elim assump_17
  cases assump_4
  case intro assump_21 assump_22 =>
    cases assump_2
    case intro assump_29 assump_30 =>
      cases assump_29
      case intro assump_31 assump_32 =>
        cases assump_31
        case intro assump_33 assump_34 =>
          apply False.elim assump_33


variable (p2 p0 p5 p4 p3 : Prop)
theorem file20_79210 : (((((False → False) ∧ (p2 → False)) → False) → False) → ((((False ∧ p5) → (p3 ∧ True)) ∨ ((p3 ∧ p5) → False)) ∨ (((p0 → True) ∧ (False ∨ p4)) → ((p0 ∧ p0) → False)))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  apply And.intro
  cases assump_4
  case intro assump_5 assump_6 =>
    apply False.elim assump_5
  apply True.intro


variable (p4 p7 p3 p2 p1 p6 p5 : Prop)
theorem file20_79628 : ((((((p6 → False) → (False ∨ True)) ∨ ((p1 ∨ p1) ∧ (p4 → False))) → False) ∧ ((((p4 ∨ p5) ∧ (p7 → False)) → ((p3 ∧ p5) → False)) ∨ (((p6 → p2) → (p5 → False)) ∧ ((p2 ∨ p6) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      have assump_42 : (((p6 → False) → (False ∨ True)) ∨ ((p1 ∨ p1) ∧ (p4 → False))) := by
        apply Or.inl
        intro assump_12
        apply Or.inr
        apply True.intro
      let assump_11 := assump_2 assump_42
      apply False.elim assump_11
    case inr assump_7 =>
      cases assump_7
      case intro assump_18 assump_19 =>
        have assump_43 : (((p6 → False) → (False ∨ True)) ∨ ((p1 ∨ p1) ∧ (p4 → False))) := by
          apply Or.inl
          intro assump_36
          apply Or.inr
          apply True.intro
        let assump_35 := assump_2 assump_43
        apply False.elim assump_35


variable (p3 p7 p6 p2 p1 : Prop)
theorem file20_80612 : ((((((p2 → p7) ∨ (p6 → p1)) → False) ∨ (((p6 → p7) → (False → False)) → False)) ∧ ((((p1 → True) → False) ∧ ((False → False) → False)) ∧ (((p6 → p6) ∧ (p1 ∨ p3)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          have assump_52 : (False → False) := by
            intro assump_23
            apply False.elim assump_23
          let assump_22 := assump_11 assump_52
          apply False.elim assump_22
    case inr assump_5 =>
      cases assump_3
      case intro assump_31 assump_32 =>
        cases assump_31
        case intro assump_33 assump_34 =>
          have assump_53 : (False → False) := by
            intro assump_46
            apply False.elim assump_46
          let assump_45 := assump_34 assump_53
          apply False.elim assump_45


variable (p1 p0 p2 p3 p6 p5 p4 : Prop)
theorem file20_81651 : (((((False → p6) ∧ (False → p5)) → False) → (((p1 ∨ p6) ∧ (True → False)) → False)) ∨ ((((p4 ∨ p2) ∨ (True ∨ p6)) ∨ ((p4 → False) → (p0 ∨ p3))) ∧ (((p5 → p5) → False) → ((p3 → False) ∧ (False ∨ True))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      have assump_39 : ((False → p6) ∧ (False → p5)) := by
        apply And.intro
        intro assump_14
        apply False.elim assump_14
        intro assump_17
        apply False.elim assump_17
      let assump_13 := assump_1 assump_39
      apply False.elim assump_13
    case inr assump_6 =>
      have assump_40 : ((False → p6) ∧ (False → p5)) := by
        apply And.intro
        intro assump_30
        apply False.elim assump_30
        intro assump_33
        apply False.elim assump_33
      let assump_29 := assump_1 assump_40
      apply False.elim assump_29


variable (p3 p4 p7 p1 p5 p0 p2 : Prop)
theorem file20_82645 : (((((p4 → False) ∧ (True → False)) ∧ ((p5 → False) ∧ (False ∧ p4))) ∨ (((p3 → False) ∧ (p7 ∨ p3)) → False)) → ((((p0 → p0) → False) → False) ∨ (((p2 ∨ p5) ∨ (p7 ∧ p1)) → False))) := by
  intro assump_71
  cases assump_71
  case inl assump_72 =>
    cases assump_72
    case intro assump_74 assump_75 =>
      cases assump_74
      case intro assump_76 assump_77 =>
        cases assump_75
        case intro assump_82 assump_83 =>
          cases assump_83
          case intro assump_86 assump_87 =>
            apply False.elim assump_86
  case inr assump_73 =>
    apply Or.inl
    intro assump_92
    have assump_102 : (p0 → p0) := by
      intro assump_96
      exact assump_96
    let assump_95 := assump_92 assump_102
    apply False.elim assump_95


variable (p1 p3 p5 p7 p2 p0 p6 : Prop)
theorem file20_83464 : ((((((p6 ∧ p3) ∨ (p5 ∧ p2)) ∧ ((p7 ∨ p1) → False)) ∨ (((False ∨ True) ∨ (p1 → False)) ∧ ((p3 → p0) ∧ (p1 ∧ p1)))) ∧ ((((p6 → p5) ∨ (p2 ∨ True)) → ((p0 → False) → (p7 → p7))) → False)) → False) := by
  intro assump_13
  cases assump_13
  case intro assump_14 assump_15 =>
    cases assump_14
    case inl assump_16 =>
      cases assump_16
      case intro assump_18 assump_19 =>
        cases assump_18
        case inl assump_20 =>
          cases assump_20
          case intro assump_22 assump_23 =>
            have assump_162 : (((p6 → p5) ∨ (p2 ∨ True)) → ((p0 → False) → (p7 → p7))) := by
              intro assump_33
              intro assump_34
              intro assump_35
              cases assump_33
              case inl assump_40 =>
                exact assump_35
              case inr assump_41 =>
                cases assump_41
                case inl assump_44 =>
                  exact assump_35
                case inr assump_45 =>
                  exact assump_35
            let assump_32 := assump_15 assump_162
            apply False.elim assump_32
        case inr assump_21 =>
          cases assump_21
          case intro assump_53 assump_54 =>
            have assump_163 : (((p6 → p5) ∨ (p2 ∨ True)) → ((p0 → False) → (p7 → p7))) := by
              intro assump_64
              intro assump_65
              intro assump_66
              cases assump_64
              case inl assump_71 =>
                exact assump_66
              case inr assump_72 =>
                cases assump_72
                case inl assump_75 =>
                  exact assump_66
                case inr assump_76 =>
                  exact assump_66
            let assump_63 := assump_15 assump_163
            apply False.elim assump_63
    case inr assump_17 =>
      cases assump_17
      case intro assump_84 assump_85 =>
        cases assump_84
        case inl assump_86 =>
          cases assump_86
          case inl assump_88 =>
            apply False.elim assump_88
          case inr assump_89 =>
            cases assump_85
            case intro assump_94 assump_95 =>
              cases assump_95
              case intro assump_98 assump_99 =>
                have assump_164 : (((p6 → p5) ∨ (p2 ∨ True)) → ((p0 → False) → (p7 → p7))) := by
                  intro assump_107
                  intro assump_108
                  intro assump_109
                  cases assump_107
                  case inl assump_114 =>
                    exact assump_109
                  case inr assump_115 =>
                    cases assump_115
                    case inl assump_118 =>
                      exact assump_109
                    case inr assump_119 =>
                      exact assump_109
                let assump_106 := assump_15 assump_164
                apply False.elim assump_106
        case inr assump_87 =>
          cases assump_85
          case intro assump_129 assump_130 =>
            cases assump_130
            case intro assump_133 assump_134 =>
              have assump_165 : (((p6 → p5) ∨ (p2 ∨ True)) → ((p0 → False) → (p7 → p7))) := by
                intro assump_142
                intro assump_143
                intro assump_144
                cases assump_142
                case inl assump_149 =>
                  exact assump_144
                case inr assump_150 =>
                  cases assump_150
                  case inl assump_153 =>
                    exact assump_144
                  case inr assump_154 =>
                    exact assump_144
              let assump_141 := assump_15 assump_165
              apply False.elim assump_141


variable (p6 p4 p7 p0 p1 p5 p2 : Prop)
theorem file20_87178 : (((((p1 ∧ p0) → False) ∨ ((False → True) → (p5 → False))) → False) → ((((p0 ∨ p0) ∧ (p6 ∧ p6)) → ((p1 → False) → False)) ∨ (((p4 → False) → (p0 → p7)) ∨ ((True → True) ∨ (p2 ∨ False))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_4
  case intro assump_8 assump_9 =>
    cases assump_8
    case inl assump_10 =>
      cases assump_9
      case intro assump_14 assump_15 =>
        have assump_76 : (((p1 ∧ p0) → False) ∨ ((False → True) → (p5 → False))) := by
          apply Or.inl
          intro assump_25
          cases assump_25
          case intro assump_26 assump_27 =>
            have assump_77 : p1 := by
              exact assump_26
            let assump_37 := assump_5 assump_77
            apply False.elim assump_37
        let assump_24 := assump_1 assump_76
        apply False.elim assump_24
    case inr assump_11 =>
      cases assump_9
      case intro assump_46 assump_47 =>
        have assump_78 : (((p1 ∧ p0) → False) ∨ ((False → True) → (p5 → False))) := by
          apply Or.inl
          intro assump_57
          cases assump_57
          case intro assump_58 assump_59 =>
            have assump_79 : p1 := by
              exact assump_58
            let assump_69 := assump_5 assump_79
            apply False.elim assump_69
        let assump_56 := assump_1 assump_78
        apply False.elim assump_56


variable (p2 p3 p6 p7 p5 : Prop)
theorem file20_88618 : ((((((p3 → p2) → False) → False) → (((p3 → p6) ∧ (p6 → p7)) ∧ ((p5 → p6) ∧ (True → False)))) ∧ ((((True ∨ p5) → (False ∧ p7)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_20 : (((True ∨ p5) → (False ∧ p7)) → False) := by
      intro assump_9
      have assump_21 : (True ∨ p5) := by
        apply Or.inl
        apply True.intro
      let assump_12 := assump_9 assump_21
      let assump_13 := And.left assump_12
      apply False.elim assump_13
    let assump_8 := assump_3 assump_20
    apply False.elim assump_8


variable (p7 p1 p2 p5 p6 p0 p3 : Prop)
theorem file20_89269 : ((((((True ∨ p7) ∧ (False → False)) → False) → (((p0 ∧ p6) → (p3 ∨ p2)) ∨ ((p5 → False) → (p1 ∧ p1)))) → False) → False) := by
  intro assump_1
  have assump_27 : ((((True ∨ p7) ∧ (False → False)) → False) → (((p0 ∧ p6) → (p3 ∨ p2)) ∨ ((p5 → False) → (p1 ∧ p1)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      have assump_28 : ((True ∨ p7) ∧ (False → False)) := by
        apply And.intro
        apply Or.inl
        apply True.intro
        intro assump_18
        apply False.elim assump_18
      let assump_17 := assump_5 assump_28
      apply False.elim assump_17
  let assump_4 := assump_1 assump_27
  apply False.elim assump_4


variable (p7 p5 p3 p2 p6 p1 p0 p4 : Prop)
theorem file20_90046 : (((((True ∨ p5) ∧ (False ∨ p6)) ∨ ((False → False) ∧ (False → p3))) ∧ (((p1 ∧ p5) → False) → ((p1 → True) ∧ (False → False)))) → ((((p5 ∨ p3) ∧ (p4 ∧ False)) ∧ ((p4 → p0) → (p5 → False))) → (((p5 ∨ True) ∧ (p7 → False)) → ((p7 ∨ p4) ∨ (p2 → p0))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_4
    case inl assump_6 =>
      cases assump_2
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
    case inr assump_7 =>
      cases assump_2
      case intro assump_38 assump_39 =>
        cases assump_38
        case intro assump_40 assump_41 =>
          cases assump_40
          case inl assump_42 =>
            cases assump_41
            case intro assump_46 assump_47 =>
              apply False.elim assump_47
          case inr assump_43 =>
            cases assump_41
            case intro assump_54 assump_55 =>
              apply False.elim assump_55


variable (p5 p6 p0 p2 p7 : Prop)
theorem file20_91423 : ((((((False → p2) → False) ∨ ((p5 ∧ True) → False)) → False) ∧ ((((p2 → p7) → False) → ((p0 → False) ∨ (p6 → p2))) ∧ (((True ∧ True) ∨ (p2 ∧ p0)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_16 : ((True ∧ True) ∨ (p2 ∧ p0)) := by
        apply Or.inl
        apply And.intro
        apply True.intro
        apply True.intro
      let assump_12 := assump_7 assump_16
      apply False.elim assump_12


theorem file20_91969 : (((((False → False) → False) → False) → False) → False) := by
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


variable (p4 p3 : Prop)
theorem file20_92406 : ((((((p3 → p4) → (True → True)) → False) → False) → False) → False) := by
  intro assump_28
  have assump_44 : ((((p3 → p4) → (True → True)) → False) → False) := by
    intro assump_32
    have assump_45 : ((p3 → p4) → (True → True)) := by
      intro assump_36
      intro assump_37
      apply True.intro
    let assump_35 := assump_32 assump_45
    apply False.elim assump_35
  let assump_31 := assump_28 assump_44
  apply False.elim assump_31


variable (p3 p5 p0 p2 p6 p4 p1 p7 : Prop)
theorem file20_92919 : ((((((False ∧ p3) → False) → False) ∧ (((p6 ∨ p2) ∨ (p1 → False)) ∧ ((False → False) → False))) ∧ ((((p2 ∨ p2) → (p5 → p7)) ∧ ((False → p5) ∨ (True → p0))) ∨ (((True ∧ True) ∨ (p4 → False)) ∨ ((p4 → True) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_10
          case inl assump_12 =>
            cases assump_3
            case inl assump_18 =>
              cases assump_18
              case intro assump_20 assump_21 =>
                cases assump_21
                case inl assump_24 =>
                  have assump_223 : (False → False) := by
                    intro assump_31
                    apply False.elim assump_31
                  let assump_30 := assump_9 assump_223
                  apply False.elim assump_30
                case inr assump_25 =>
                  have assump_224 : (False → False) := by
                    intro assump_43
                    apply False.elim assump_43
                  let assump_42 := assump_9 assump_224
                  apply False.elim assump_42
            case inr assump_19 =>
              cases assump_19
              case inl assump_49 =>
                cases assump_49
                case inl assump_51 =>
                  cases assump_51
                  case intro assump_53 assump_54 =>
                    have assump_225 : (False → False) := by
                      intro assump_60
                      apply False.elim assump_60
                    let assump_59 := assump_9 assump_225
                    apply False.elim assump_59
                case inr assump_52 =>
                  have assump_226 : (False → False) := by
                    intro assump_70
                    apply False.elim assump_70
                  let assump_69 := assump_9 assump_226
                  apply False.elim assump_69
              case inr assump_50 =>
                have assump_227 : (p4 → True) := by
                  intro assump_79
                  apply True.intro
                let assump_78 := assump_50 assump_227
                apply False.elim assump_78
          case inr assump_13 =>
            cases assump_3
            case inl assump_87 =>
              cases assump_87
              case intro assump_89 assump_90 =>
                cases assump_90
                case inl assump_93 =>
                  have assump_228 : (False → False) := by
                    intro assump_101
                    apply False.elim assump_101
                  let assump_100 := assump_9 assump_228
                  apply False.elim assump_100
                case inr assump_94 =>
                  have assump_229 : (False → False) := by
                    intro assump_114
                    apply False.elim assump_114
                  let assump_113 := assump_9 assump_229
                  apply False.elim assump_113
            case inr assump_88 =>
              cases assump_88
              case inl assump_120 =>
                cases assump_120
                case inl assump_122 =>
                  cases assump_122
                  case intro assump_124 assump_125 =>
                    have assump_230 : (False → False) := by
                      intro assump_131
                      apply False.elim assump_131
                    let assump_130 := assump_9 assump_230
                    apply False.elim assump_130
                case inr assump_123 =>
                  have assump_231 : (False → False) := by
                    intro assump_141
                    apply False.elim assump_141
                  let assump_140 := assump_9 assump_231
                  apply False.elim assump_140
              case inr assump_121 =>
                have assump_232 : (p4 → True) := by
                  intro assump_150
                  apply True.intro
                let assump_149 := assump_121 assump_232
                apply False.elim assump_149
        case inr assump_11 =>
          cases assump_3
          case inl assump_158 =>
            cases assump_158
            case intro assump_160 assump_161 =>
              cases assump_161
              case inl assump_164 =>
                have assump_233 : (False → False) := by
                  intro assump_171
                  apply False.elim assump_171
                let assump_170 := assump_9 assump_233
                apply False.elim assump_170
              case inr assump_165 =>
                have assump_234 : (False → False) := by
                  intro assump_183
                  apply False.elim assump_183
                let assump_182 := assump_9 assump_234
                apply False.elim assump_182
          case inr assump_159 =>
            cases assump_159
            case inl assump_189 =>
              cases assump_189
              case inl assump_191 =>
                cases assump_191
                case intro assump_193 assump_194 =>
                  have assump_235 : (False → False) := by
                    intro assump_200
                    apply False.elim assump_200
                  let assump_199 := assump_9 assump_235
                  apply False.elim assump_199
              case inr assump_192 =>
                have assump_236 : (False → False) := by
                  intro assump_210
                  apply False.elim assump_210
                let assump_209 := assump_9 assump_236
                apply False.elim assump_209
            case inr assump_190 =>
              have assump_237 : (p4 → True) := by
                intro assump_219
                apply True.intro
              let assump_218 := assump_190 assump_237
              apply False.elim assump_218


variable (p1 p7 p5 p3 p6 p4 p0 : Prop)
theorem file20_98859 : (((((p4 ∧ False) → (False → False)) → ((p4 ∨ True) → False)) ∧ (((p3 ∧ p4) ∧ (p1 → p4)) ∨ ((p3 ∧ p6) → False))) → ((((p0 → False) → (p7 ∧ p6)) → False) ∧ (((True → p6) → (False ∨ False)) ∧ ((p5 → p4) → False)))) := by
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
        case intro assump_13 assump_14 =>
          have assump_131 : ((p4 ∧ False) → (False → False)) := by
            intro assump_25
            intro assump_26
            apply False.elim assump_26
          let assump_24 := assump_5 assump_131
          have assump_132 : (p4 ∨ True) := by
            apply Or.inl
            exact assump_14
          let assump_29 := assump_24 assump_132
          apply False.elim assump_29
    case inr assump_10 =>
      have assump_133 : ((p4 ∧ False) → (False → False)) := by
        intro assump_37
        intro assump_38
        apply False.elim assump_38
      let assump_36 := assump_5 assump_133
      have assump_134 : (p4 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_41 := assump_36 assump_134
      apply False.elim assump_41
  apply And.intro
  intro assump_45
  cases assump_1
  case intro assump_48 assump_49 =>
    cases assump_49
    case inl assump_52 =>
      cases assump_52
      case intro assump_54 assump_55 =>
        cases assump_54
        case intro assump_56 assump_57 =>
          have assump_135 : ((p4 ∧ False) → (False → False)) := by
            intro assump_68
            intro assump_69
            apply False.elim assump_69
          let assump_67 := assump_48 assump_135
          have assump_136 : (p4 ∨ True) := by
            apply Or.inl
            exact assump_57
          let assump_72 := assump_67 assump_136
          apply False.elim assump_72
    case inr assump_53 =>
      have assump_137 : ((p4 ∧ False) → (False → False)) := by
        intro assump_80
        intro assump_81
        apply False.elim assump_81
      let assump_79 := assump_48 assump_137
      have assump_138 : (p4 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_84 := assump_79 assump_138
      apply False.elim assump_84
  intro assump_88
  cases assump_1
  case intro assump_91 assump_92 =>
    cases assump_92
    case inl assump_95 =>
      cases assump_95
      case intro assump_97 assump_98 =>
        cases assump_97
        case intro assump_99 assump_100 =>
          have assump_139 : ((p4 ∧ False) → (False → False)) := by
            intro assump_111
            intro assump_112
            apply False.elim assump_112
          let assump_110 := assump_91 assump_139
          have assump_140 : (p4 ∨ True) := by
            apply Or.inl
            exact assump_100
          let assump_115 := assump_110 assump_140
          apply False.elim assump_115
    case inr assump_96 =>
      have assump_141 : ((p4 ∧ False) → (False → False)) := by
        intro assump_123
        intro assump_124
        apply False.elim assump_124
      let assump_122 := assump_91 assump_141
      have assump_142 : (p4 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_127 := assump_122 assump_142
      apply False.elim assump_127


variable (p1 p0 p2 p7 p6 p4 p5 p3 : Prop)
theorem file20_102264 : (((((p2 ∧ p3) → False) → False) → (((False → False) → False) ∧ ((p0 → p0) ∨ (p4 → p7)))) → ((((False → False) → False) → ((p1 ∧ p6) → (p2 ∨ p5))) ∨ (((p7 → False) → False) → False))) := by
  intro assump_7
  apply Or.inl
  intro assump_10
  intro assump_11
  cases assump_11
  case intro assump_12 assump_13 =>
    have assump_27 : (False → False) := by
      intro assump_21
      apply False.elim assump_21
    let assump_20 := assump_10 assump_27
    apply False.elim assump_20


variable (p0 p7 p1 p5 p4 p2 : Prop)
theorem file20_102805 : (((((p1 ∨ p0) ∨ (p7 ∨ p7)) ∧ ((p2 → p4) → (p4 ∧ p2))) ∧ (((False ∧ p0) → (p5 ∧ p7)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          have assump_88 : ((False ∧ p0) → (p5 ∧ p7)) := by
            intro assump_17
            apply And.intro
            cases assump_17
            case intro assump_18 assump_19 =>
              apply False.elim assump_18
            cases assump_17
            case intro assump_22 assump_23 =>
              apply False.elim assump_22
          let assump_16 := assump_3 assump_88
          apply False.elim assump_16
        case inr assump_9 =>
          have assump_89 : ((False ∧ p0) → (p5 ∧ p7)) := by
            intro assump_36
            apply And.intro
            cases assump_36
            case intro assump_37 assump_38 =>
              apply False.elim assump_37
            cases assump_36
            case intro assump_41 assump_42 =>
              apply False.elim assump_41
          let assump_35 := assump_3 assump_89
          apply False.elim assump_35
      case inr assump_7 =>
        cases assump_7
        case inl assump_48 =>
          have assump_90 : ((False ∧ p0) → (p5 ∧ p7)) := by
            intro assump_57
            apply And.intro
            cases assump_57
            case intro assump_58 assump_59 =>
              apply False.elim assump_58
            cases assump_57
            case intro assump_62 assump_63 =>
              apply False.elim assump_62
          let assump_56 := assump_3 assump_90
          apply False.elim assump_56
        case inr assump_49 =>
          have assump_91 : ((False ∧ p0) → (p5 ∧ p7)) := by
            intro assump_76
            apply And.intro
            cases assump_76
            case intro assump_77 assump_78 =>
              apply False.elim assump_77
            cases assump_76
            case intro assump_81 assump_82 =>
              apply False.elim assump_81
          let assump_75 := assump_3 assump_91
          apply False.elim assump_75


variable (p7 p6 p3 p0 p4 : Prop)
theorem file20_105049 : ((((((p3 ∧ p4) → (p3 → p4)) → False) → (((p6 ∨ p0) ∧ (True → p7)) → ((p3 ∧ p0) ∨ (p4 ∧ p3)))) → False) → False) := by
  intro assump_1
  have assump_54 : ((((p3 ∧ p4) → (p3 → p4)) → False) → (((p6 ∨ p0) ∧ (True → p7)) → ((p3 ∧ p0) ∨ (p4 ∧ p3)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        have assump_55 : ((p3 ∧ p4) → (p3 → p4)) := by
          intro assump_18
          intro assump_19
          cases assump_18
          case intro assump_22 assump_23 =>
            exact assump_23
        let assump_17 := assump_5 assump_55
        apply False.elim assump_17
      case inr assump_10 =>
        have assump_56 : ((p3 ∧ p4) → (p3 → p4)) := by
          intro assump_38
          intro assump_39
          cases assump_38
          case intro assump_42 assump_43 =>
            exact assump_43
        let assump_37 := assump_5 assump_56
        apply False.elim assump_37
  let assump_4 := assump_1 assump_54
  apply False.elim assump_4


variable (p7 p4 p2 p6 p0 p5 : Prop)
theorem file20_106163 : ((((((p0 ∧ p0) ∧ (True ∨ p2)) → False) ∧ (((p6 → False) → False) ∨ ((p5 → False) ∨ (p4 ∧ p7)))) ∧ ((((p4 ∨ False) → (False → False)) ∨ ((True ∧ p0) → (p0 → p4))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        have assump_52 : (((p4 ∨ False) → (False → False)) ∨ ((True ∧ p0) → (p0 → p4))) := by
          apply Or.inl
          intro assump_15
          intro assump_16
          apply False.elim assump_16
        let assump_14 := assump_3 assump_52
        apply False.elim assump_14
      case inr assump_9 =>
        cases assump_9
        case inl assump_22 =>
          have assump_53 : (((p4 ∨ False) → (False → False)) ∨ ((True ∧ p0) → (p0 → p4))) := by
            apply Or.inl
            intro assump_29
            intro assump_30
            apply False.elim assump_30
          let assump_28 := assump_3 assump_53
          apply False.elim assump_28
        case inr assump_23 =>
          cases assump_23
          case intro assump_36 assump_37 =>
            have assump_54 : (((p4 ∨ False) → (False → False)) ∨ ((True ∧ p0) → (p0 → p4))) := by
              apply Or.inl
              intro assump_45
              intro assump_46
              apply False.elim assump_46
            let assump_44 := assump_3 assump_54
            apply False.elim assump_44


variable (p5 p2 p7 p3 p6 p4 : Prop)
theorem file20_107658 : ((((((True ∧ p2) → (p4 ∧ p7)) → ((p2 → False) → (p2 → p5))) ∨ (((False ∨ p4) → (p2 → False)) → ((p3 ∨ True) ∨ (p3 ∨ p6)))) → False) → False) := by
  intro assump_1
  have assump_25 : ((((True ∧ p2) → (p4 ∧ p7)) → ((p2 → False) → (p2 → p5))) ∨ (((False ∨ p4) → (p2 → False)) → ((p3 ∨ True) ∨ (p3 ∨ p6)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    have assump_26 : p2 := by
      exact assump_7
    let assump_18 := assump_6 assump_26
    apply False.elim assump_18
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p0 p1 p7 p4 : Prop)
theorem file20_108283 : (((((p7 → True) ∨ (p7 ∨ p1)) ∨ ((p4 ∨ p0) ∧ (False ∨ False))) → False) → False) := by
  intro assump_1
  have assump_9 : (((p7 → True) ∨ (p7 ∨ p1)) ∨ ((p4 ∨ p0) ∧ (False ∨ False))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_9
  apply False.elim assump_4


variable (p2 p5 p7 p6 p1 p4 : Prop)
theorem file20_108668 : ((((((True ∨ p2) ∧ (p1 ∨ p1)) ∨ ((p6 → p1) → False)) → (((p4 ∧ False) ∨ (True ∧ False)) → ((p5 ∧ p7) ∧ (p5 → False)))) → False) → False) := by
  intro assump_1
  have assump_55 : ((((True ∨ p2) ∧ (p1 ∨ p1)) ∨ ((p6 → p1) → False)) → (((p4 ∧ False) ∨ (True ∧ False)) → ((p5 ∧ p7) ∧ (p5 → False)))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    apply And.intro
    cases assump_6
    case inl assump_7 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        apply False.elim assump_10
    case inr assump_8 =>
      cases assump_8
      case intro assump_15 assump_16 =>
        apply False.elim assump_16
    cases assump_6
    case inl assump_21 =>
      cases assump_21
      case intro assump_23 assump_24 =>
        apply False.elim assump_24
    case inr assump_22 =>
      cases assump_22
      case intro assump_29 assump_30 =>
        apply False.elim assump_30
    intro assump_35
    cases assump_6
    case inl assump_38 =>
      cases assump_38
      case intro assump_40 assump_41 =>
        apply False.elim assump_41
    case inr assump_39 =>
      cases assump_39
      case intro assump_46 assump_47 =>
        apply False.elim assump_47
  let assump_4 := assump_1 assump_55
  apply False.elim assump_4


variable (p7 p0 p1 p4 p5 p3 p2 p6 : Prop)
theorem file20_109989 : ((((((p2 → False) → (p1 → p2)) ∧ ((p5 ∨ p3) ∨ (False ∧ False))) ∨ (((p4 ∧ p2) ∧ (p6 → False)) → ((p2 ∨ True) → False))) ∧ ((((p0 ∨ p0) → (p6 ∨ p7)) → False) ∧ (((p7 ∧ True) ∧ (p0 ∧ False)) ∧ ((False → False) ∨ (p3 ∧ True))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case inl assump_10 =>
          cases assump_10
          case inl assump_12 =>
            cases assump_3
            case intro assump_16 assump_17 =>
              cases assump_17
              case intro assump_20 assump_21 =>
                cases assump_20
                case intro assump_22 assump_23 =>
                  cases assump_22
                  case intro assump_24 assump_25 =>
                    cases assump_23
                    case intro assump_30 assump_31 =>
                      apply False.elim assump_31
          case inr assump_13 =>
            cases assump_3
            case intro assump_38 assump_39 =>
              cases assump_39
              case intro assump_42 assump_43 =>
                cases assump_42
                case intro assump_44 assump_45 =>
                  cases assump_44
                  case intro assump_46 assump_47 =>
                    cases assump_45
                    case intro assump_52 assump_53 =>
                      apply False.elim assump_53
        case inr assump_11 =>
          cases assump_11
          case intro assump_58 assump_59 =>
            apply False.elim assump_58
    case inr assump_5 =>
      cases assump_3
      case intro assump_64 assump_65 =>
        cases assump_65
        case intro assump_68 assump_69 =>
          cases assump_68
          case intro assump_70 assump_71 =>
            cases assump_70
            case intro assump_72 assump_73 =>
              cases assump_71
              case intro assump_78 assump_79 =>
                apply False.elim assump_79


variable (p2 p3 p0 p5 p7 p1 p4 p6 : Prop)
theorem file20_112082 : (((((True → False) ∨ (p6 ∨ p4)) → ((p0 → False) → False)) → (((p7 ∧ False) ∧ (p3 ∧ True)) → False)) ∧ ((((p6 ∨ True) ∨ (p7 ∨ p2)) ∧ ((p1 ∨ p5) ∧ (p5 ∧ p6))) → (((p6 → False) → (p1 ∨ p2)) ∨ ((p6 ∧ p7) → False)))) := by
  apply And.intro
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      apply False.elim assump_6
  intro assump_11
  cases assump_11
  case intro assump_12 assump_13 =>
    cases assump_12
    case inl assump_14 =>
      cases assump_14
      case inl assump_16 =>
        cases assump_13
        case intro assump_20 assump_21 =>
          cases assump_20
          case inl assump_22 =>
            cases assump_21
            case intro assump_26 assump_27 =>
              apply Or.inl
              intro assump_32
              apply Or.inl
              exact assump_22
          case inr assump_23 =>
            cases assump_21
            case intro assump_37 assump_38 =>
              apply Or.inl
              intro assump_43
              have assump_144 : p6 := by
                exact assump_38
              let assump_46 := assump_43 assump_144
              apply False.elim assump_46
      case inr assump_17 =>
        cases assump_13
        case intro assump_52 assump_53 =>
          cases assump_52
          case inl assump_54 =>
            cases assump_53
            case intro assump_58 assump_59 =>
              apply Or.inl
              intro assump_64
              apply Or.inl
              exact assump_54
          case inr assump_55 =>
            cases assump_53
            case intro assump_69 assump_70 =>
              apply Or.inl
              intro assump_75
              have assump_145 : p6 := by
                exact assump_70
              let assump_78 := assump_75 assump_145
              apply False.elim assump_78
    case inr assump_15 =>
      cases assump_15
      case inl assump_82 =>
        cases assump_13
        case intro assump_86 assump_87 =>
          cases assump_86
          case inl assump_88 =>
            cases assump_87
            case intro assump_92 assump_93 =>
              apply Or.inl
              intro assump_98
              apply Or.inl
              exact assump_88
          case inr assump_89 =>
            cases assump_87
            case intro assump_103 assump_104 =>
              apply Or.inl
              intro assump_109
              have assump_146 : p6 := by
                exact assump_104
              let assump_112 := assump_109 assump_146
              apply False.elim assump_112
      case inr assump_83 =>
        cases assump_13
        case intro assump_118 assump_119 =>
          cases assump_118
          case inl assump_120 =>
            cases assump_119
            case intro assump_124 assump_125 =>
              apply Or.inl
              intro assump_130
              apply Or.inl
              exact assump_120
          case inr assump_121 =>
            cases assump_119
            case intro assump_135 assump_136 =>
              apply Or.inl
              intro assump_141
              apply Or.inr
              exact assump_83


variable (p7 p4 p6 p3 : Prop)
theorem file20_115320 : ((((((False ∨ p4) → (p4 → p7)) ∧ ((False → p6) ∧ (True → False))) → (((p4 ∨ p7) ∨ (p6 → p6)) → ((True ∨ p7) ∨ (p3 ∧ p3)))) → False) → False) := by
  intro assump_1
  have assump_50 : ((((False ∨ p4) → (p4 → p7)) ∧ ((False → p6) ∧ (True → False))) → (((p4 ∨ p7) ∨ (p6 → p6)) → ((True ∨ p7) ∨ (p3 ∧ p3)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_5
        case intro assump_13 assump_14 =>
          cases assump_14
          case intro assump_17 assump_18 =>
            apply Or.inl
            apply Or.inl
            apply True.intro
      case inr assump_10 =>
        cases assump_5
        case intro assump_25 assump_26 =>
          cases assump_26
          case intro assump_29 assump_30 =>
            apply Or.inl
            apply Or.inl
            apply True.intro
    case inr assump_8 =>
      cases assump_5
      case intro assump_37 assump_38 =>
        cases assump_38
        case intro assump_41 assump_42 =>
          apply Or.inl
          apply Or.inl
          apply True.intro
  let assump_4 := assump_1 assump_50
  apply False.elim assump_4


variable (p7 p1 p4 p2 p6 p3 p0 p5 : Prop)
theorem file20_116572 : (((((True → p1) ∧ (p7 → p3)) → ((p7 → p5) ∨ (p3 → False))) → (((p5 → p5) ∧ (p1 ∨ p7)) ∨ ((p4 ∧ p6) → (p1 ∧ True)))) → ((((p4 ∧ False) ∨ (p7 ∧ p0)) ∨ ((False → p4) ∨ (p0 ∨ True))) → (((p3 ∧ p7) ∧ (p2 ∧ False)) → ((p1 → False) ∧ (True ∧ p2))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  apply And.intro
  intro assump_4
  cases assump_3
  case intro assump_7 assump_8 =>
    cases assump_7
    case intro assump_9 assump_10 =>
      cases assump_8
      case intro assump_15 assump_16 =>
        apply False.elim assump_16
  apply And.intro
  apply True.intro
  cases assump_3
  case intro assump_21 assump_22 =>
    cases assump_21
    case intro assump_23 assump_24 =>
      cases assump_22
      case intro assump_29 assump_30 =>
        apply False.elim assump_30


variable (p1 p4 p7 p2 p0 p3 p5 p6 : Prop)
theorem file20_117421 : ((((((p2 ∨ False) ∧ (p0 ∨ False)) ∧ ((p7 → False) → (p1 ∧ p0))) ∧ (((p1 ∨ p4) ∨ (p0 ∨ p4)) → ((p6 → False) → False))) ∧ ((((p5 → False) → (p2 ∨ p2)) → ((p6 → p2) ∧ (p2 ∧ p4))) ∧ (((p1 → False) → False) ∧ ((p3 ∨ p1) → False)))) → False) := by
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
            cases assump_9
            case inl assump_14 =>
              cases assump_3
              case intro assump_22 assump_23 =>
                cases assump_23
                case intro assump_26 assump_27 =>
                  have assump_49 : (p1 → False) := by
                    intro assump_34
                    have assump_50 : (p3 ∨ p1) := by
                      apply Or.inr
                      exact assump_34
                    let assump_38 := assump_27 assump_50
                    apply False.elim assump_38
                  let assump_33 := assump_26 assump_49
                  apply False.elim assump_33
            case inr assump_15 =>
              apply False.elim assump_15
          case inr assump_11 =>
            apply False.elim assump_11


variable (p7 p1 p3 p2 p4 p0 p5 : Prop)
theorem file20_118814 : ((((((p5 ∨ p5) ∨ (True ∧ p5)) ∧ ((p4 → False) ∨ (p3 ∧ p5))) ∨ (((True → True) ∨ (p2 ∧ True)) ∧ ((p7 ∨ p1) ∨ (p0 → True)))) → False) → False) := by
  intro assump_4
  have assump_13 : ((((p5 ∨ p5) ∨ (True ∧ p5)) ∧ ((p4 → False) ∨ (p3 ∧ p5))) ∨ (((True → True) ∨ (p2 ∧ True)) ∧ ((p7 ∨ p1) ∨ (p0 → True)))) := by
    apply Or.inr
    apply And.intro
    apply Or.inl
    intro assump_8
    apply True.intro
    apply Or.inr
    intro assump_9
    apply True.intro
  let assump_7 := assump_4 assump_13
  apply False.elim assump_7


variable (p4 p5 p0 p1 : Prop)
theorem file20_119394 : (((((p1 → False) → (False → False)) ∨ ((p0 ∨ p0) → False)) ∨ (((p5 → False) → False) ∨ ((p1 ∧ p5) → (False ∧ p1)))) ∧ ((((True ∨ True) → (True → False)) → False) ∨ (((p1 → p4) ∨ (False ∨ p0)) → False))) := by
  apply And.intro
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  apply False.elim assump_2
  apply Or.inl
  intro assump_5
  have assump_13 : (True ∨ True) := by
    apply Or.inl
    apply True.intro
  let assump_8 := assump_5 assump_13
  have assump_14 : True := by
    apply True.intro
  let assump_9 := assump_8 assump_14
  apply False.elim assump_9


variable (p1 p0 p5 p3 p4 p7 p6 p2 : Prop)
theorem file20_120041 : (((((p5 → p3) → (p3 → p7)) ∨ ((p7 → False) → (p6 ∨ True))) → False) → ((((p3 → False) ∧ (p2 → False)) → ((p1 ∧ p0) ∨ (p5 → p3))) ∨ (((p5 ∧ p7) ∨ (True → p4)) → ((p5 ∧ p5) ∨ (p1 → p0))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply Or.inr
    intro assump_11
    have assump_36 : (((p5 → p3) → (p3 → p7)) ∨ ((p7 → False) → (p6 ∨ True))) := by
      apply Or.inl
      intro assump_18
      intro assump_19
      have assump_37 : p3 := by
        exact assump_19
      let assump_29 := assump_5 assump_37
      apply False.elim assump_29
    let assump_17 := assump_1 assump_36
    apply False.elim assump_17


