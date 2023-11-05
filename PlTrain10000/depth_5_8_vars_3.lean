variable (p5 p3 p1 p6 p4 p7 : Prop)
theorem file3_44 : (((((True → False) ∧ (p7 ∨ p7)) → ((p5 ∨ True) ∧ (p1 ∨ p4))) ∨ (((p3 ∨ True) ∨ (False ∨ p5)) ∧ ((p1 → True) → False))) ∨ ((((True → p3) ∧ (p3 ∨ p5)) → ((p6 ∨ p1) ∨ (p3 ∨ True))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      apply Or.inr
      apply True.intro
    case inr assump_7 =>
      apply Or.inr
      apply True.intro
  cases assump_1
  case intro assump_12 assump_13 =>
    cases assump_13
    case inl assump_16 =>
      have assump_32 : True := by
        apply True.intro
      let assump_21 := assump_12 assump_32
      apply False.elim assump_21
    case inr assump_17 =>
      have assump_33 : True := by
        apply True.intro
      let assump_28 := assump_12 assump_33
      apply False.elim assump_28


variable (p3 p6 p0 p4 p2 : Prop)
theorem file3_959 : ((((((False → p2) ∨ (p0 ∧ False)) → False) → (((p6 ∧ p3) → (p4 ∧ p6)) → False)) → False) → False) := by
  intro assump_1
  have assump_21 : ((((False → p2) ∨ (p0 ∧ False)) → False) → (((p6 ∧ p3) → (p4 ∧ p6)) → False)) := by
    intro assump_5
    intro assump_6
    have assump_22 : ((False → p2) ∨ (p0 ∧ False)) := by
      apply Or.inl
      intro assump_12
      apply False.elim assump_12
    let assump_11 := assump_5 assump_22
    apply False.elim assump_11
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p7 p0 p5 p4 p3 p2 p6 : Prop)
theorem file3_1551 : (((((True ∨ p2) ∨ (p5 ∨ False)) → False) ∧ (((p2 ∧ p6) → False) ∨ ((False ∧ p2) → False))) → ((((p6 → False) ∨ (p3 ∧ p6)) ∧ ((p4 ∧ p0) → (p0 ∨ True))) ∨ (((p0 → False) ∨ (False → p7)) ∧ ((p5 ∨ p7) → False)))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      apply Or.inl
      apply And.intro
      apply Or.inl
      intro assump_10
      have assump_44 : ((True ∨ p2) ∨ (p5 ∨ False)) := by
        apply Or.inl
        apply Or.inl
        apply True.intro
      let assump_15 := assump_2 assump_44
      apply False.elim assump_15
      intro assump_19
      cases assump_19
      case intro assump_20 assump_21 =>
        apply Or.inl
        exact assump_21
    case inr assump_7 =>
      apply Or.inl
      apply And.intro
      apply Or.inl
      intro assump_28
      have assump_45 : ((True ∨ p2) ∨ (p5 ∨ False)) := by
        apply Or.inl
        apply Or.inl
        apply True.intro
      let assump_33 := assump_2 assump_45
      apply False.elim assump_33
      intro assump_37
      cases assump_37
      case intro assump_38 assump_39 =>
        apply Or.inl
        exact assump_39


variable (p4 p7 p1 p0 p3 : Prop)
theorem file3_2782 : ((((((True ∨ False) → False) → False) → False) ∧ ((((p7 → False) ∧ (p0 ∨ p4)) ∧ ((p4 ∨ p3) ∧ (False → False))) ∨ (((p7 → False) ∨ (True ∨ p3)) ∨ ((True ∧ False) ∧ (p7 ∨ p1))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_11
          case inl assump_14 =>
            cases assump_9
            case intro assump_18 assump_19 =>
              cases assump_18
              case inl assump_20 =>
                have assump_159 : (((True ∨ False) → False) → False) := by
                  intro assump_31
                  have assump_160 : (True ∨ False) := by
                    apply Or.inl
                    apply True.intro
                  let assump_34 := assump_31 assump_160
                  apply False.elim assump_34
                let assump_30 := assump_2 assump_159
                apply False.elim assump_30
              case inr assump_21 =>
                have assump_161 : (((True ∨ False) → False) → False) := by
                  intro assump_50
                  have assump_162 : (True ∨ False) := by
                    apply Or.inl
                    apply True.intro
                  let assump_53 := assump_50 assump_162
                  apply False.elim assump_53
                let assump_49 := assump_2 assump_161
                apply False.elim assump_49
          case inr assump_15 =>
            cases assump_9
            case intro assump_62 assump_63 =>
              cases assump_62
              case inl assump_64 =>
                have assump_163 : (((True ∨ False) → False) → False) := by
                  intro assump_75
                  have assump_164 : (True ∨ False) := by
                    apply Or.inl
                    apply True.intro
                  let assump_78 := assump_75 assump_164
                  apply False.elim assump_78
                let assump_74 := assump_2 assump_163
                apply False.elim assump_74
              case inr assump_65 =>
                have assump_165 : (((True ∨ False) → False) → False) := by
                  intro assump_94
                  have assump_166 : (True ∨ False) := by
                    apply Or.inl
                    apply True.intro
                  let assump_97 := assump_94 assump_166
                  apply False.elim assump_97
                let assump_93 := assump_2 assump_165
                apply False.elim assump_93
    case inr assump_7 =>
      cases assump_7
      case inl assump_104 =>
        cases assump_104
        case inl assump_106 =>
          have assump_167 : (((True ∨ False) → False) → False) := by
            intro assump_112
            have assump_168 : (True ∨ False) := by
              apply Or.inl
              apply True.intro
            let assump_115 := assump_112 assump_168
            apply False.elim assump_115
          let assump_111 := assump_2 assump_167
          apply False.elim assump_111
        case inr assump_107 =>
          cases assump_107
          case inl assump_122 =>
            have assump_169 : (((True ∨ False) → False) → False) := by
              intro assump_127
              have assump_170 : (True ∨ False) := by
                apply Or.inl
                apply True.intro
              let assump_130 := assump_127 assump_170
              apply False.elim assump_130
            let assump_126 := assump_2 assump_169
            apply False.elim assump_126
          case inr assump_123 =>
            have assump_171 : (((True ∨ False) → False) → False) := by
              intro assump_141
              have assump_172 : (True ∨ False) := by
                apply Or.inl
                apply True.intro
              let assump_144 := assump_141 assump_172
              apply False.elim assump_144
            let assump_140 := assump_2 assump_171
            apply False.elim assump_140
      case inr assump_105 =>
        cases assump_105
        case intro assump_151 assump_152 =>
          cases assump_151
          case intro assump_153 assump_154 =>
            apply False.elim assump_154


variable (p4 p0 p3 p1 p6 p7 p5 : Prop)
theorem file3_7102 : (((((False ∧ p7) → False) ∧ ((p1 ∨ p5) ∧ (False ∧ False))) ∨ (((p4 → False) → (True ∧ True)) ∨ ((p5 ∧ False) → False))) ∨ ((((p0 ∨ p5) → False) → False) → (((p7 → False) ∧ (False ∧ p6)) → ((p3 → False) ∨ (p6 → p6))))) := by
  apply Or.inl
  apply Or.inr
  apply Or.inl
  intro assump_6
  apply And.intro
  apply True.intro
  apply True.intro


variable (p2 p5 p3 p6 p1 : Prop)
theorem file3_7501 : ((((((p6 → False) ∨ (p5 → p3)) → ((p2 ∨ p5) → (True → p6))) → (((p6 → False) → (False ∨ True)) ∨ ((False → p1) ∨ (p3 ∧ p6)))) → False) → False) := by
  intro assump_46
  have assump_59 : ((((p6 → False) ∨ (p5 → p3)) → ((p2 ∨ p5) → (True → p6))) → (((p6 → False) → (False ∨ True)) ∨ ((False → p1) ∨ (p3 ∧ p6)))) := by
    intro assump_50
    apply Or.inl
    intro assump_53
    apply Or.inr
    apply True.intro
  let assump_49 := assump_46 assump_59
  apply False.elim assump_49


variable (p3 p6 p0 p2 p7 p4 p5 : Prop)
theorem file3_8044 : (((((False → False) ∨ (True → True)) → False) ∨ (((p3 ∨ p3) → (p0 → False)) ∧ ((p4 → p5) → False))) → ((((p0 ∨ p4) ∧ (p3 ∨ p6)) ∧ ((p2 → p7) ∧ (p3 ∨ p0))) → (((p3 ∧ True) → (False → False)) ∧ ((p2 → False) → (False → False))))) := by
  intro assump_7
  intro assump_8
  apply And.intro
  intro assump_9
  intro assump_10
  apply False.elim assump_10
  intro assump_13
  intro assump_14
  apply False.elim assump_14


variable (p1 p0 p7 p4 : Prop)
theorem file3_8513 : (((((p4 → p1) ∨ (p7 ∧ p0)) ∧ ((p0 → False) ∧ (p4 ∧ p1))) → False) → ((((p1 → False) → False) → ((p1 ∧ False) → False)) ∨ (((p4 ∧ True) → (True → False)) → ((True → False) → False)))) := by
  intro assump_31
  apply Or.inl
  intro assump_34
  intro assump_35
  cases assump_35
  case intro assump_36 assump_37 =>
    apply False.elim assump_37


variable (p3 p5 p4 p7 : Prop)
theorem file3_8910 : (((((False → p3) ∨ (True ∨ p5)) ∨ ((p4 ∧ p7) → (p7 → p5))) → False) → False) := by
  intro assump_1
  have assump_11 : (((False → p3) ∨ (True ∨ p5)) ∨ ((p4 ∧ p7) → (p7 → p5))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p7 p0 p1 p5 : Prop)
theorem file3_9294 : ((((((p5 ∧ p7) → False) → ((p1 → True) → (p7 ∨ True))) ∨ (((True → False) → (False → p7)) ∨ ((p7 → p5) → (p0 ∧ True)))) → False) → False) := by
  intro assump_37
  have assump_50 : ((((p5 ∧ p7) → False) → ((p1 → True) → (p7 ∨ True))) ∨ (((True → False) → (False → p7)) ∨ ((p7 → p5) → (p0 ∧ True)))) := by
    apply Or.inl
    intro assump_41
    intro assump_42
    apply Or.inr
    apply True.intro
  let assump_40 := assump_37 assump_50
  apply False.elim assump_40


variable (p3 p6 p7 p5 p2 p0 p4 : Prop)
theorem file3_9825 : (((((p2 → False) → False) → ((p0 ∨ p5) ∨ (False → p3))) → False) → ((((False → p2) ∨ (p7 ∨ p6)) ∨ ((p0 ∨ p4) → (p6 → p4))) → (((p6 → True) ∧ (p4 ∨ p0)) → ((p6 → p4) ∨ (False → p7))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_5
    case inl assump_8 =>
      cases assump_2
      case inl assump_12 =>
        cases assump_12
        case inl assump_14 =>
          apply Or.inl
          intro assump_20
          exact assump_8
        case inr assump_15 =>
          cases assump_15
          case inl assump_23 =>
            apply Or.inl
            intro assump_29
            exact assump_8
          case inr assump_24 =>
            apply Or.inl
            intro assump_36
            exact assump_8
      case inr assump_13 =>
        apply Or.inl
        intro assump_43
        exact assump_8
    case inr assump_9 =>
      cases assump_2
      case inl assump_48 =>
        cases assump_48
        case inl assump_50 =>
          apply Or.inl
          intro assump_56
          have assump_114 : (((p2 → False) → False) → ((p0 ∨ p5) ∨ (False → p3))) := by
            intro assump_61
            apply Or.inl
            apply Or.inl
            exact assump_9
          let assump_60 := assump_1 assump_114
          apply False.elim assump_60
        case inr assump_51 =>
          cases assump_51
          case inl assump_67 =>
            apply Or.inl
            intro assump_73
            have assump_115 : (((p2 → False) → False) → ((p0 ∨ p5) ∨ (False → p3))) := by
              intro assump_78
              apply Or.inl
              apply Or.inl
              exact assump_9
            let assump_77 := assump_1 assump_115
            apply False.elim assump_77
          case inr assump_68 =>
            apply Or.inl
            intro assump_88
            have assump_116 : (((p2 → False) → False) → ((p0 ∨ p5) ∨ (False → p3))) := by
              intro assump_93
              apply Or.inl
              apply Or.inl
              exact assump_9
            let assump_92 := assump_1 assump_116
            apply False.elim assump_92
      case inr assump_49 =>
        apply Or.inl
        intro assump_103
        have assump_117 : (((p2 → False) → False) → ((p0 ∨ p5) ∨ (False → p3))) := by
          intro assump_108
          apply Or.inl
          apply Or.inl
          exact assump_9
        let assump_107 := assump_1 assump_117
        apply False.elim assump_107


variable (p4 p2 p7 p6 p0 p5 p1 p3 : Prop)
theorem file3_12382 : (((((p6 ∧ p1) ∨ (p0 ∨ p0)) ∧ ((True ∨ p6) ∨ (p5 ∧ p6))) → False) → ((((False → p4) ∨ (p7 ∧ p0)) → False) → (((p3 ∧ True) → (p0 → False)) ∧ ((p2 → False) ∨ (p7 → False))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  intro assump_4
  cases assump_3
  case intro assump_7 assump_8 =>
    have assump_37 : (((p6 ∧ p1) ∨ (p0 ∨ p0)) ∧ ((True ∨ p6) ∨ (p5 ∧ p6))) := by
      apply And.intro
      apply Or.inr
      apply Or.inl
      exact assump_4
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_17 := assump_1 assump_37
    apply False.elim assump_17
  apply Or.inl
  intro assump_25
  have assump_38 : ((False → p4) ∨ (p7 ∧ p0)) := by
    apply Or.inl
    intro assump_31
    apply False.elim assump_31
  let assump_30 := assump_2 assump_38
  apply False.elim assump_30


variable (p0 p1 p7 p4 p6 p2 p5 p3 : Prop)
theorem file3_13277 : (((((p1 ∧ p4) → (p4 → False)) ∧ ((True ∧ p3) ∧ (p2 ∧ p0))) ∨ (((p7 ∨ p1) → False) ∧ ((p7 ∨ p3) → False))) → ((((p4 ∨ False) ∧ (p5 ∧ p6)) ∧ ((False → p3) → False)) → (((p1 → False) ∧ (p0 → False)) → False))) := by
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
            cases assump_1
            case inl assump_26 =>
              cases assump_26
              case intro assump_28 assump_29 =>
                cases assump_29
                case intro assump_32 assump_33 =>
                  cases assump_32
                  case intro assump_34 assump_35 =>
                    cases assump_33
                    case intro assump_40 assump_41 =>
                      have assump_74 : (False → p3) := by
                        intro assump_51
                        apply False.elim assump_51
                      let assump_50 := assump_11 assump_74
                      apply False.elim assump_50
            case inr assump_27 =>
              cases assump_27
              case intro assump_57 assump_58 =>
                have assump_75 : (False → p3) := by
                  intro assump_66
                  apply False.elim assump_66
                let assump_65 := assump_11 assump_75
                apply False.elim assump_65
        case inr assump_15 =>
          apply False.elim assump_15


variable (p5 p7 p6 p2 p0 p3 p1 : Prop)
theorem file3_14958 : (((((False ∧ False) → (True ∨ p0)) → False) → False) ∨ ((((p6 → False) → (False → False)) → False) ∧ (((p7 ∧ p3) → (p6 ∧ p5)) → ((p1 ∨ True) ∨ (p3 ∨ p2))))) := by
  apply Or.inl
  intro assump_5
  have assump_17 : ((False ∧ False) → (True ∨ p0)) := by
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      apply False.elim assump_10
  let assump_8 := assump_5 assump_17
  apply False.elim assump_8


variable (p4 p5 p3 p0 p7 p1 p2 p6 : Prop)
theorem file3_15450 : (((((p2 → p0) ∨ (True → p3)) ∧ ((p5 ∧ p6) ∧ (p5 → False))) → (((False ∨ False) → (True ∧ p7)) → ((p7 → p3) ∧ (p4 ∧ p6)))) ∨ ((((p2 ∨ False) ∧ (p2 ∨ p1)) ∨ ((False ∨ p2) ∨ (p4 ∧ p6))) ∧ (((False → p3) ∧ (p2 ∧ p6)) → ((p4 ∧ p6) → (True → p3))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  cases assump_1
  case intro assump_8 assump_9 =>
    cases assump_8
    case inl assump_10 =>
      cases assump_9
      case intro assump_14 assump_15 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          have assump_112 : p5 := by
            exact assump_16
          let assump_24 := assump_15 assump_112
          apply False.elim assump_24
    case inr assump_11 =>
      cases assump_9
      case intro assump_30 assump_31 =>
        cases assump_30
        case intro assump_32 assump_33 =>
          have assump_113 : p5 := by
            exact assump_32
          let assump_40 := assump_31 assump_113
          apply False.elim assump_40
  apply And.intro
  cases assump_1
  case intro assump_46 assump_47 =>
    cases assump_46
    case inl assump_48 =>
      cases assump_47
      case intro assump_52 assump_53 =>
        cases assump_52
        case intro assump_54 assump_55 =>
          have assump_114 : p5 := by
            exact assump_54
          let assump_62 := assump_53 assump_114
          apply False.elim assump_62
    case inr assump_49 =>
      cases assump_47
      case intro assump_68 assump_69 =>
        cases assump_68
        case intro assump_70 assump_71 =>
          have assump_115 : p5 := by
            exact assump_70
          let assump_78 := assump_69 assump_115
          apply False.elim assump_78
  cases assump_1
  case intro assump_84 assump_85 =>
    cases assump_84
    case inl assump_86 =>
      cases assump_85
      case intro assump_90 assump_91 =>
        cases assump_90
        case intro assump_92 assump_93 =>
          exact assump_93
    case inr assump_87 =>
      cases assump_85
      case intro assump_102 assump_103 =>
        cases assump_102
        case intro assump_104 assump_105 =>
          exact assump_105


variable (p1 p5 p3 p6 p7 p2 p0 p4 : Prop)
theorem file3_17664 : (((((p0 ∧ p0) ∨ (p0 → p1)) ∨ ((p4 → False) → (p0 ∨ p3))) → False) → ((((p2 → False) ∨ (p7 → False)) → ((p3 ∧ p2) → False)) ∧ (((p0 → False) → (p7 ∨ p6)) ∧ ((p0 ∧ p5) → (p7 → p1))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_2
    case inl assump_10 =>
      have assump_77 : (((p0 ∧ p0) ∨ (p0 → p1)) ∨ ((p4 → False) → (p0 ∨ p3))) := by
        apply Or.inl
        apply Or.inr
        intro assump_17
        have assump_78 : (((p0 ∧ p0) ∨ (p0 → p1)) ∨ ((p4 → False) → (p0 ∨ p3))) := by
          apply Or.inl
          apply Or.inl
          apply And.intro
          exact assump_17
          exact assump_17
        let assump_21 := assump_1 assump_78
        apply False.elim assump_21
      let assump_16 := assump_1 assump_77
      apply False.elim assump_16
    case inr assump_11 =>
      have assump_79 : (((p0 ∧ p0) ∨ (p0 → p1)) ∨ ((p4 → False) → (p0 ∨ p3))) := by
        apply Or.inl
        apply Or.inr
        intro assump_33
        have assump_80 : (((p0 ∧ p0) ∨ (p0 → p1)) ∨ ((p4 → False) → (p0 ∨ p3))) := by
          apply Or.inl
          apply Or.inl
          apply And.intro
          exact assump_33
          exact assump_33
        let assump_37 := assump_1 assump_80
        apply False.elim assump_37
      let assump_32 := assump_1 assump_79
      apply False.elim assump_32
  apply And.intro
  intro assump_44
  have assump_81 : (((p0 ∧ p0) ∨ (p0 → p1)) ∨ ((p4 → False) → (p0 ∨ p3))) := by
    apply Or.inl
    apply Or.inr
    intro assump_50
    have assump_82 : (((p0 ∧ p0) ∨ (p0 → p1)) ∨ ((p4 → False) → (p0 ∨ p3))) := by
      apply Or.inl
      apply Or.inl
      apply And.intro
      exact assump_50
      exact assump_50
    let assump_54 := assump_1 assump_82
    apply False.elim assump_54
  let assump_49 := assump_1 assump_81
  apply False.elim assump_49
  intro assump_61
  intro assump_62
  cases assump_61
  case intro assump_65 assump_66 =>
    have assump_83 : (((p0 ∧ p0) ∨ (p0 → p1)) ∨ ((p4 → False) → (p0 ∨ p3))) := by
      apply Or.inl
      apply Or.inl
      apply And.intro
      exact assump_65
      exact assump_65
    let assump_73 := assump_1 assump_83
    apply False.elim assump_73


variable (p6 p2 p5 p4 p3 p7 p0 : Prop)
theorem file3_19975 : (((((p5 → False) → False) → False) ∨ (((p6 → False) → False) ∧ ((p2 ∧ p4) → False))) → ((((p0 ∨ False) ∧ (p0 → p6)) → ((p3 → True) → (p7 ∧ p2))) → (((p0 → p3) ∨ (False → False)) → ((False ∨ False) → (p0 → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  intro assump_5
  cases assump_4
  case inl assump_8 =>
    apply False.elim assump_8
  case inr assump_9 =>
    apply False.elim assump_9


variable (p1 p3 p4 p7 p2 : Prop)
theorem file3_20462 : ((((((p1 ∧ p3) ∨ (False → p4)) ∨ ((p4 → p2) → (p7 → False))) ∨ (((True → False) → False) ∨ ((p2 ∧ p3) → False))) → False) → False) := by
  intro assump_5
  have assump_15 : ((((p1 ∧ p3) ∨ (False → p4)) ∨ ((p4 → p2) → (p7 → False))) ∨ (((True → False) → False) ∨ ((p2 ∧ p3) → False))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    intro assump_9
    apply False.elim assump_9
  let assump_8 := assump_5 assump_15
  apply False.elim assump_8


variable (p1 p7 p5 p3 p2 p4 p6 p0 : Prop)
theorem file3_20983 : (((((p6 ∧ p5) → (False ∨ p2)) → False) ∧ (((p2 ∨ p0) ∨ (True ∨ True)) → False)) → ((((p1 → p1) → False) → ((p5 ∧ False) ∨ (p4 → False))) ∧ (((p4 ∨ p7) ∧ (True → p3)) → False))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    apply Or.inr
    intro assump_11
    have assump_52 : ((p2 ∨ p0) ∨ (True ∨ True)) := by
      apply Or.inr
      apply Or.inl
      apply True.intro
    let assump_15 := assump_6 assump_52
    apply False.elim assump_15
  intro assump_19
  cases assump_19
  case intro assump_20 assump_21 =>
    cases assump_20
    case inl assump_22 =>
      cases assump_1
      case intro assump_28 assump_29 =>
        have assump_53 : ((p2 ∨ p0) ∨ (True ∨ True)) := by
          apply Or.inr
          apply Or.inl
          apply True.intro
        let assump_34 := assump_29 assump_53
        apply False.elim assump_34
    case inr assump_23 =>
      cases assump_1
      case intro assump_42 assump_43 =>
        have assump_54 : ((p2 ∨ p0) ∨ (True ∨ True)) := by
          apply Or.inr
          apply Or.inl
          apply True.intro
        let assump_48 := assump_43 assump_54
        apply False.elim assump_48


variable (p4 p6 p2 : Prop)
theorem file3_22234 : (((((False → False) → (p6 → p2)) → ((p6 → p6) ∨ (True → p4))) → False) → False) := by
  intro assump_1
  have assump_14 : (((False → False) → (p6 → p2)) → ((p6 → p6) ∨ (True → p4))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    exact assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p1 p0 p4 p6 p5 : Prop)
theorem file3_22618 : (((((p6 ∨ p1) ∨ (False → False)) ∨ ((False → p5) → (p0 ∨ p4))) → False) → False) := by
  intro assump_1
  have assump_11 : (((p6 ∨ p1) ∨ (False → False)) ∨ ((False → p5) → (p0 ∨ p4))) := by
    apply Or.inl
    apply Or.inr
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p5 p7 p3 p4 p1 : Prop)
theorem file3_23013 : (((((p5 → True) ∨ (p7 → False)) → ((False ∧ p1) ∧ (p7 → False))) → (((p4 → False) ∧ (p3 ∨ p7)) → False)) ∨ ((((p1 → False) → False) ∧ ((p4 ∨ p5) ∨ (p3 ∨ p3))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case inl assump_7 =>
      have assump_31 : ((p5 → True) ∨ (p7 → False)) := by
        apply Or.inl
        intro assump_14
        apply True.intro
      let assump_13 := assump_1 assump_31
      let assump_15 := And.left assump_13
      let assump_16 := And.left assump_15
      apply False.elim assump_16
    case inr assump_8 =>
      have assump_32 : ((p5 → True) ∨ (p7 → False)) := by
        apply Or.inl
        intro assump_25
        apply True.intro
      let assump_24 := assump_1 assump_32
      let assump_26 := And.left assump_24
      let assump_27 := And.left assump_26
      apply False.elim assump_27


variable (p2 p6 p7 p5 p3 : Prop)
theorem file3_23988 : (((((p2 ∧ True) ∧ (True → False)) → False) → (((False → p5) ∧ (True ∧ True)) → False)) → ((((p3 ∨ p7) ∨ (p6 ∨ p5)) ∨ ((p2 → p2) ∧ (p7 → False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_5
      case inl assump_7 =>
        have assump_150 : (((p2 ∧ True) ∧ (True → False)) → False) := by
          intro assump_14
          cases assump_14
          case intro assump_15 assump_16 =>
            cases assump_15
            case intro assump_17 assump_18 =>
              have assump_151 : True := by
                apply True.intro
              let assump_25 := assump_16 assump_151
              apply False.elim assump_25
        let assump_13 := assump_1 assump_150
        have assump_152 : ((False → p5) ∧ (True ∧ True)) := by
          apply And.intro
          intro assump_30
          apply False.elim assump_30
          apply And.intro
          apply True.intro
          apply True.intro
        let assump_29 := assump_13 assump_152
        apply False.elim assump_29
      case inr assump_8 =>
        have assump_153 : (((p2 ∧ True) ∧ (True → False)) → False) := by
          intro assump_41
          cases assump_41
          case intro assump_42 assump_43 =>
            cases assump_42
            case intro assump_44 assump_45 =>
              have assump_154 : True := by
                apply True.intro
              let assump_52 := assump_43 assump_154
              apply False.elim assump_52
        let assump_40 := assump_1 assump_153
        have assump_155 : ((False → p5) ∧ (True ∧ True)) := by
          apply And.intro
          intro assump_57
          apply False.elim assump_57
          apply And.intro
          apply True.intro
          apply True.intro
        let assump_56 := assump_40 assump_155
        apply False.elim assump_56
    case inr assump_6 =>
      cases assump_6
      case inl assump_63 =>
        have assump_156 : (((p2 ∧ True) ∧ (True → False)) → False) := by
          intro assump_70
          cases assump_70
          case intro assump_71 assump_72 =>
            cases assump_71
            case intro assump_73 assump_74 =>
              have assump_157 : True := by
                apply True.intro
              let assump_81 := assump_72 assump_157
              apply False.elim assump_81
        let assump_69 := assump_1 assump_156
        have assump_158 : ((False → p5) ∧ (True ∧ True)) := by
          apply And.intro
          intro assump_86
          apply False.elim assump_86
          apply And.intro
          apply True.intro
          apply True.intro
        let assump_85 := assump_69 assump_158
        apply False.elim assump_85
      case inr assump_64 =>
        have assump_159 : (((p2 ∧ True) ∧ (True → False)) → False) := by
          intro assump_97
          cases assump_97
          case intro assump_98 assump_99 =>
            cases assump_98
            case intro assump_100 assump_101 =>
              have assump_160 : True := by
                apply True.intro
              let assump_108 := assump_99 assump_160
              apply False.elim assump_108
        let assump_96 := assump_1 assump_159
        have assump_161 : ((False → p5) ∧ (True ∧ True)) := by
          apply And.intro
          intro assump_113
          apply False.elim assump_113
          apply And.intro
          apply True.intro
          apply True.intro
        let assump_112 := assump_96 assump_161
        apply False.elim assump_112
  case inr assump_4 =>
    cases assump_4
    case intro assump_119 assump_120 =>
      have assump_162 : (((p2 ∧ True) ∧ (True → False)) → False) := by
        intro assump_128
        cases assump_128
        case intro assump_129 assump_130 =>
          cases assump_129
          case intro assump_131 assump_132 =>
            have assump_163 : True := by
              apply True.intro
            let assump_139 := assump_130 assump_163
            apply False.elim assump_139
      let assump_127 := assump_1 assump_162
      have assump_164 : ((False → p5) ∧ (True ∧ True)) := by
        apply And.intro
        intro assump_144
        apply False.elim assump_144
        apply And.intro
        apply True.intro
        apply True.intro
      let assump_143 := assump_127 assump_164
      apply False.elim assump_143


variable (p7 p3 p2 p0 p6 p4 : Prop)
theorem file3_28420 : (((((False → p0) ∨ (True → False)) → False) → (((p3 → True) → False) → ((p7 → False) → (p7 ∧ p2)))) ∨ ((((p6 ∨ p6) ∧ (p2 → False)) ∨ ((False ∨ p0) → (True → False))) → (((p3 ∨ True) → (p6 → p4)) ∧ ((p6 ∨ p6) ∧ (p6 ∧ p2))))) := by
  apply Or.inl
  intro assump_5
  intro assump_6
  intro assump_7
  apply And.intro
  have assump_34 : ((False → p0) ∨ (True → False)) := by
    apply Or.inl
    intro assump_15
    apply False.elim assump_15
  let assump_14 := assump_5 assump_34
  apply False.elim assump_14
  have assump_35 : ((False → p0) ∨ (True → False)) := by
    apply Or.inl
    intro assump_28
    apply False.elim assump_28
  let assump_27 := assump_5 assump_35
  apply False.elim assump_27


variable (p0 p7 p4 p3 p6 p2 : Prop)
theorem file3_29178 : (((((p3 ∨ p7) ∨ (p0 ∨ p3)) ∧ ((p0 → p3) → False)) → False) → ((((p6 ∨ p0) → (False → p4)) → ((p2 ∧ False) ∨ (False ∧ p0))) → (((False ∧ p4) → False) ∨ ((p4 → p7) → False)))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    apply False.elim assump_8


variable (p6 p4 p3 p2 : Prop)
theorem file3_29559 : (((((p4 → False) ∧ (p3 → p6)) ∧ ((p2 → False) → False)) ∧ (((True → False) → False) → ((p2 ∨ False) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        have assump_45 : (p2 → False) := by
          intro assump_26
          have assump_46 : ((True → False) → False) := by
            intro assump_31
            have assump_47 : True := by
              apply True.intro
            let assump_34 := assump_31 assump_47
            apply False.elim assump_34
          let assump_30 := assump_3 assump_46
          have assump_48 : (p2 ∨ False) := by
            apply Or.inl
            exact assump_26
          let assump_38 := assump_30 assump_48
          apply False.elim assump_38
        let assump_25 := assump_5 assump_45
        apply False.elim assump_25


variable (p1 p0 p7 p5 p6 p2 p3 : Prop)
theorem file3_30553 : (((((p6 ∧ False) ∧ (p0 ∧ p6)) → False) ∨ (((p5 ∧ p5) ∨ (p7 → p5)) → False)) → ((((p1 → p7) → (p6 → False)) ∧ ((p3 ∧ False) ∧ (p2 ∧ True))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        apply False.elim assump_10


variable (p7 p6 p1 p3 p0 p2 : Prop)
theorem file3_31003 : (((((p2 ∨ p1) ∨ (p0 → False)) → ((True → False) → (p0 ∧ p3))) ∨ (((p3 ∧ p0) ∨ (p1 → p7)) ∨ ((False → False) ∧ (p3 ∨ p6)))) ∨ ((((p0 → False) → False) → ((p6 ∨ p6) → False)) → (((p2 → p0) → False) ∨ ((True → False) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  cases assump_1
  case inl assump_5 =>
    cases assump_5
    case inl assump_7 =>
      have assump_57 : True := by
        apply True.intro
      let assump_12 := assump_2 assump_57
      apply False.elim assump_12
    case inr assump_8 =>
      have assump_58 : True := by
        apply True.intro
      let assump_19 := assump_2 assump_58
      apply False.elim assump_19
  case inr assump_6 =>
    have assump_59 : True := by
      apply True.intro
    let assump_26 := assump_2 assump_59
    apply False.elim assump_26
  cases assump_1
  case inl assump_32 =>
    cases assump_32
    case inl assump_34 =>
      have assump_60 : True := by
        apply True.intro
      let assump_39 := assump_2 assump_60
      apply False.elim assump_39
    case inr assump_35 =>
      have assump_61 : True := by
        apply True.intro
      let assump_46 := assump_2 assump_61
      apply False.elim assump_46
  case inr assump_33 =>
    have assump_62 : True := by
      apply True.intro
    let assump_53 := assump_2 assump_62
    apply False.elim assump_53


variable (p5 p4 p0 p1 p3 p7 : Prop)
theorem file3_32434 : (((((p4 → p4) → False) → False) → False) → ((((p3 → False) ∧ (p3 ∨ p5)) ∧ ((p0 → False) ∧ (p7 ∧ p0))) ∧ (((p0 ∧ p1) → False) → False))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  apply And.intro
  intro assump_2
  have assump_107 : (((p4 → p4) → False) → False) := by
    intro assump_8
    have assump_108 : (p4 → p4) := by
      intro assump_12
      exact assump_12
    let assump_11 := assump_8 assump_108
    apply False.elim assump_11
  let assump_7 := assump_1 assump_107
  apply False.elim assump_7
  have assump_109 : (((p4 → p4) → False) → False) := by
    intro assump_24
    have assump_110 : (p4 → p4) := by
      intro assump_28
      exact assump_28
    let assump_27 := assump_24 assump_110
    apply False.elim assump_27
  let assump_23 := assump_1 assump_109
  apply False.elim assump_23
  apply And.intro
  intro assump_37
  have assump_111 : (((p4 → p4) → False) → False) := by
    intro assump_43
    have assump_112 : (p4 → p4) := by
      intro assump_47
      exact assump_47
    let assump_46 := assump_43 assump_112
    apply False.elim assump_46
  let assump_42 := assump_1 assump_111
  apply False.elim assump_42
  apply And.intro
  have assump_113 : (((p4 → p4) → False) → False) := by
    intro assump_59
    have assump_114 : (p4 → p4) := by
      intro assump_63
      exact assump_63
    let assump_62 := assump_59 assump_114
    apply False.elim assump_62
  let assump_58 := assump_1 assump_113
  apply False.elim assump_58
  have assump_115 : (((p4 → p4) → False) → False) := by
    intro assump_75
    have assump_116 : (p4 → p4) := by
      intro assump_79
      exact assump_79
    let assump_78 := assump_75 assump_116
    apply False.elim assump_78
  let assump_74 := assump_1 assump_115
  apply False.elim assump_74
  intro assump_88
  have assump_117 : (((p4 → p4) → False) → False) := by
    intro assump_94
    have assump_118 : (p4 → p4) := by
      intro assump_98
      exact assump_98
    let assump_97 := assump_94 assump_118
    apply False.elim assump_97
  let assump_93 := assump_1 assump_117
  apply False.elim assump_93


variable (p1 p6 p5 p0 p3 p4 p7 p2 : Prop)
theorem file3_34592 : (((((p6 → p5) ∨ (p7 → p1)) ∧ ((p1 → False) ∨ (p4 → False))) → (((False ∧ True) → False) ∨ ((p2 ∨ p7) → False))) ∨ ((((p0 ∧ p2) ∨ (False → p4)) ∧ ((p4 → p3) ∧ (False ∧ True))) ∧ (((p2 → False) ∨ (p2 ∨ False)) ∧ ((p3 ∧ p7) ∨ (p6 → p7))))) := by
  apply Or.inl
  intro assump_15
  cases assump_15
  case intro assump_16 assump_17 =>
    cases assump_16
    case inl assump_18 =>
      cases assump_17
      case inl assump_22 =>
        apply Or.inl
        intro assump_26
        cases assump_26
        case intro assump_27 assump_28 =>
          apply False.elim assump_27
      case inr assump_23 =>
        apply Or.inl
        intro assump_33
        cases assump_33
        case intro assump_34 assump_35 =>
          apply False.elim assump_34
    case inr assump_19 =>
      cases assump_17
      case inl assump_40 =>
        apply Or.inl
        intro assump_44
        cases assump_44
        case intro assump_45 assump_46 =>
          apply False.elim assump_45
      case inr assump_41 =>
        apply Or.inl
        intro assump_51
        cases assump_51
        case intro assump_52 assump_53 =>
          apply False.elim assump_52


variable (p4 p5 p6 p2 p0 p1 p7 : Prop)
theorem file3_35805 : (((((p4 ∨ p5) → False) ∨ ((True → False) → False)) → False) → ((((p1 → p6) ∧ (p0 ∧ p7)) ∧ ((p2 ∨ True) ∧ (p7 → False))) → (((p5 ∨ p6) ∧ (p2 ∨ p2)) ∨ ((p0 ∧ True) ∨ (p1 → False))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_6
      case intro assump_9 assump_10 =>
        cases assump_4
        case intro assump_15 assump_16 =>
          cases assump_15
          case inl assump_17 =>
            apply Or.inr
            apply Or.inl
            apply And.intro
            exact assump_9
            apply True.intro
          case inr assump_18 =>
            apply Or.inr
            apply Or.inl
            apply And.intro
            exact assump_9
            apply True.intro


variable (p1 p2 p7 p4 p6 : Prop)
theorem file3_36672 : (((((p2 ∨ p7) ∨ (True → False)) ∨ ((False → True) ∧ (p4 ∨ p1))) ∧ (((p6 → False) → (p7 ∨ True)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          have assump_71 : ((p6 → False) → (p7 ∨ True)) := by
            intro assump_15
            apply Or.inr
            apply True.intro
          let assump_14 := assump_3 assump_71
          apply False.elim assump_14
        case inr assump_9 =>
          have assump_72 : ((p6 → False) → (p7 ∨ True)) := by
            intro assump_26
            apply Or.inl
            exact assump_9
          let assump_25 := assump_3 assump_72
          apply False.elim assump_25
      case inr assump_7 =>
        have assump_73 : ((p6 → False) → (p7 ∨ True)) := by
          intro assump_37
          apply Or.inr
          apply True.intro
        let assump_36 := assump_3 assump_73
        apply False.elim assump_36
    case inr assump_5 =>
      cases assump_5
      case intro assump_43 assump_44 =>
        cases assump_44
        case inl assump_47 =>
          have assump_74 : ((p6 → False) → (p7 ∨ True)) := by
            intro assump_54
            apply Or.inr
            apply True.intro
          let assump_53 := assump_3 assump_74
          apply False.elim assump_53
        case inr assump_48 =>
          have assump_75 : ((p6 → False) → (p7 ∨ True)) := by
            intro assump_65
            apply Or.inr
            apply True.intro
          let assump_64 := assump_3 assump_75
          apply False.elim assump_64


variable (p5 p1 p0 p4 : Prop)
theorem file3_38406 : ((((((p0 → p4) → False) → False) ∨ (((p4 → p1) → (p0 ∨ p4)) → False)) ∧ ((((False ∧ p4) ∧ (p1 ∧ p5)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_36 : (((False ∧ p4) ∧ (p1 ∧ p5)) → False) := by
        intro assump_11
        cases assump_11
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            apply False.elim assump_14
      let assump_10 := assump_3 assump_36
      apply False.elim assump_10
    case inr assump_5 =>
      have assump_37 : (((False ∧ p4) ∧ (p1 ∧ p5)) → False) := by
        intro assump_26
        cases assump_26
        case intro assump_27 assump_28 =>
          cases assump_27
          case intro assump_29 assump_30 =>
            apply False.elim assump_29
      let assump_25 := assump_3 assump_37
      apply False.elim assump_25


variable (p0 p3 p7 p1 p5 p4 p6 : Prop)
theorem file3_39421 : (((((p3 ∧ p4) ∨ (p0 ∧ True)) → False) ∧ (((p0 ∨ p6) → False) ∧ ((p6 ∧ p7) → (p4 → False)))) → ((((p6 ∨ p4) ∧ (p4 ∧ False)) ∨ ((p1 ∨ p3) → (p5 ∧ p1))) → (((p3 ∨ True) ∧ (p3 ∧ False)) → ((True ∧ p4) ∧ (False → p7))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  apply And.intro
  apply And.intro
  apply True.intro
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_4
    case inl assump_6 =>
      cases assump_5
      case intro assump_10 assump_11 =>
        apply False.elim assump_11
    case inr assump_7 =>
      cases assump_5
      case intro assump_18 assump_19 =>
        apply False.elim assump_19
  intro assump_24
  apply False.elim assump_24


variable (p2 p1 p6 p4 p3 p7 : Prop)
theorem file3_40168 : (((((False → False) ∨ (True → False)) → False) → (((p4 ∧ p3) → (p7 ∧ p6)) ∧ ((p4 ∧ p6) → False))) ∧ ((((False → False) → False) → ((p1 ∧ p7) ∨ (True ∨ p2))) ∨ (((True → True) ∧ (p6 → p7)) ∨ ((p6 → False) → (p4 → False))))) := by
  apply And.intro
  intro assump_1
  apply And.intro
  intro assump_2
  apply And.intro
  cases assump_2
  case intro assump_3 assump_4 =>
    have assump_52 : ((False → False) ∨ (True → False)) := by
      apply Or.inl
      intro assump_12
      apply False.elim assump_12
    let assump_11 := assump_1 assump_52
    apply False.elim assump_11
  cases assump_2
  case intro assump_18 assump_19 =>
    have assump_53 : ((False → False) ∨ (True → False)) := by
      apply Or.inl
      intro assump_27
      apply False.elim assump_27
    let assump_26 := assump_1 assump_53
    apply False.elim assump_26
  intro assump_33
  cases assump_33
  case intro assump_34 assump_35 =>
    have assump_54 : ((False → False) ∨ (True → False)) := by
      apply Or.inl
      intro assump_43
      apply False.elim assump_43
    let assump_42 := assump_1 assump_54
    apply False.elim assump_42
  apply Or.inl
  intro assump_49
  apply Or.inr
  apply Or.inl
  apply True.intro


variable (p6 p4 p5 p1 p7 p2 : Prop)
theorem file3_41424 : ((((((p6 → False) ∧ (p6 → False)) ∧ ((p2 ∧ p5) ∧ (p7 ∧ p6))) → False) → ((((p5 → p2) ∧ (p1 ∨ p5)) → ((p6 ∨ p1) ∨ (p5 ∨ p4))) → False)) → False) := by
  intro assump_1
  have assump_51 : ((((p6 → False) ∧ (p6 → False)) ∧ ((p2 ∧ p5) ∧ (p7 ∧ p6))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case intro assump_14 assump_15 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            cases assump_15
            case intro assump_22 assump_23 =>
              have assump_52 : p6 := by
                exact assump_23
              let assump_32 := assump_9 assump_52
              apply False.elim assump_32
  let assump_4 := assump_1 assump_51
  have assump_53 : (((p5 → p2) ∧ (p1 ∨ p5)) → ((p6 ∨ p1) ∨ (p5 ∨ p4))) := by
    intro assump_37
    cases assump_37
    case intro assump_38 assump_39 =>
      cases assump_39
      case inl assump_42 =>
        apply Or.inl
        apply Or.inr
        exact assump_42
      case inr assump_43 =>
        apply Or.inr
        apply Or.inl
        exact assump_43
  let assump_36 := assump_4 assump_53
  apply False.elim assump_36


variable (p0 p5 p1 p7 p3 p2 p6 p4 : Prop)
theorem file3_42724 : (((((False → False) ∨ (False ∧ p4)) ∧ ((True → False) ∨ (False ∧ True))) → (((p0 ∨ p0) ∨ (p5 ∧ True)) ∨ ((p3 → False) → (p3 ∧ False)))) ∨ ((((p2 → False) → (True ∧ p6)) ∨ ((p4 → False) ∧ (p5 ∨ p5))) ∨ (((p7 → p5) ∨ (p1 ∧ p5)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case inl assump_8 =>
        apply Or.inr
        intro assump_12
        apply And.intro
        have assump_35 : True := by
          apply True.intro
        let assump_16 := assump_8 assump_35
        apply False.elim assump_16
        have assump_36 : True := by
          apply True.intro
        let assump_23 := assump_8 assump_36
        apply False.elim assump_23
      case inr assump_9 =>
        cases assump_9
        case intro assump_27 assump_28 =>
          apply False.elim assump_27
    case inr assump_5 =>
      cases assump_5
      case intro assump_31 assump_32 =>
        apply False.elim assump_31


variable (p7 p0 p6 p1 p3 p5 p2 p4 : Prop)
theorem file3_43811 : (((((p5 → p7) ∨ (True → p4)) ∨ ((p4 ∧ p7) ∧ (p7 ∨ p7))) ∧ (((p0 ∨ p0) ∧ (p3 ∧ p6)) ∧ ((True ∨ p2) → False))) → ((((p6 ∨ p4) → False) → ((True ∧ p1) ∨ (p7 → p0))) → (((p1 ∨ p1) ∧ (p3 → p5)) ∨ ((p5 → p2) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_6
        case intro assump_13 assump_14 =>
          cases assump_13
          case intro assump_15 assump_16 =>
            cases assump_15
            case inl assump_17 =>
              cases assump_16
              case intro assump_21 assump_22 =>
                apply Or.inr
                intro assump_29
                have assump_197 : (True ∨ p2) := by
                  apply Or.inl
                  apply True.intro
                let assump_33 := assump_14 assump_197
                apply False.elim assump_33
            case inr assump_18 =>
              cases assump_16
              case intro assump_39 assump_40 =>
                apply Or.inr
                intro assump_47
                have assump_198 : (True ∨ p2) := by
                  apply Or.inl
                  apply True.intro
                let assump_51 := assump_14 assump_198
                apply False.elim assump_51
      case inr assump_10 =>
        cases assump_6
        case intro assump_57 assump_58 =>
          cases assump_57
          case intro assump_59 assump_60 =>
            cases assump_59
            case inl assump_61 =>
              cases assump_60
              case intro assump_65 assump_66 =>
                apply Or.inr
                intro assump_73
                have assump_199 : (True ∨ p2) := by
                  apply Or.inl
                  apply True.intro
                let assump_77 := assump_58 assump_199
                apply False.elim assump_77
            case inr assump_62 =>
              cases assump_60
              case intro assump_83 assump_84 =>
                apply Or.inr
                intro assump_91
                have assump_200 : (True ∨ p2) := by
                  apply Or.inl
                  apply True.intro
                let assump_95 := assump_58 assump_200
                apply False.elim assump_95
    case inr assump_8 =>
      cases assump_8
      case intro assump_99 assump_100 =>
        cases assump_99
        case intro assump_101 assump_102 =>
          cases assump_100
          case inl assump_107 =>
            cases assump_6
            case intro assump_111 assump_112 =>
              cases assump_111
              case intro assump_113 assump_114 =>
                cases assump_113
                case inl assump_115 =>
                  cases assump_114
                  case intro assump_119 assump_120 =>
                    apply Or.inr
                    intro assump_127
                    have assump_201 : (True ∨ p2) := by
                      apply Or.inl
                      apply True.intro
                    let assump_131 := assump_112 assump_201
                    apply False.elim assump_131
                case inr assump_116 =>
                  cases assump_114
                  case intro assump_137 assump_138 =>
                    apply Or.inr
                    intro assump_145
                    have assump_202 : (True ∨ p2) := by
                      apply Or.inl
                      apply True.intro
                    let assump_149 := assump_112 assump_202
                    apply False.elim assump_149
          case inr assump_108 =>
            cases assump_6
            case intro assump_155 assump_156 =>
              cases assump_155
              case intro assump_157 assump_158 =>
                cases assump_157
                case inl assump_159 =>
                  cases assump_158
                  case intro assump_163 assump_164 =>
                    apply Or.inr
                    intro assump_171
                    have assump_203 : (True ∨ p2) := by
                      apply Or.inl
                      apply True.intro
                    let assump_175 := assump_156 assump_203
                    apply False.elim assump_175
                case inr assump_160 =>
                  cases assump_158
                  case intro assump_181 assump_182 =>
                    apply Or.inr
                    intro assump_189
                    have assump_204 : (True ∨ p2) := by
                      apply Or.inl
                      apply True.intro
                    let assump_193 := assump_156 assump_204
                    apply False.elim assump_193


variable (p6 p3 p0 p2 : Prop)
theorem file3_48538 : ((((((p3 → True) ∧ (p3 ∧ p2)) → False) → (((p0 ∧ p0) → (p0 ∨ p6)) ∧ ((False → False) ∨ (p3 → p3)))) → False) → False) := by
  intro assump_5
  have assump_27 : ((((p3 → True) ∧ (p3 ∧ p2)) → False) → (((p0 ∧ p0) → (p0 ∨ p6)) ∧ ((False → False) ∨ (p3 → p3)))) := by
    intro assump_9
    apply And.intro
    intro assump_10
    cases assump_10
    case intro assump_11 assump_12 =>
      apply Or.inl
      exact assump_12
    apply Or.inl
    intro assump_21
    apply False.elim assump_21
  let assump_8 := assump_5 assump_27
  apply False.elim assump_8


variable (p4 p0 p6 p7 p2 p5 : Prop)
theorem file3_49153 : (((((True → False) ∨ (True → False)) ∧ ((p6 ∧ p4) ∧ (p6 → p0))) ∧ (((p5 ∨ True) → (p7 → p2)) ∧ ((False → p6) → False))) → False) := by
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
          case intro assump_12 assump_13 =>
            cases assump_3
            case intro assump_20 assump_21 =>
              have assump_58 : (False → p6) := by
                intro assump_27
                apply False.elim assump_27
              let assump_26 := assump_21 assump_58
              apply False.elim assump_26
      case inr assump_7 =>
        cases assump_5
        case intro assump_35 assump_36 =>
          cases assump_35
          case intro assump_37 assump_38 =>
            cases assump_3
            case intro assump_45 assump_46 =>
              have assump_59 : (False → p6) := by
                intro assump_52
                apply False.elim assump_52
              let assump_51 := assump_46 assump_59
              apply False.elim assump_51


variable (p7 p6 : Prop)
theorem file3_50384 : (((((p6 → False) → False) → ((True → True) ∨ (False ∨ p7))) → False) → False) := by
  intro assump_1
  have assump_12 : (((p6 → False) → False) → ((True → True) ∨ (False ∨ p7))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    apply True.intro
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p2 p5 p1 p6 : Prop)
theorem file3_50763 : ((((((p1 → False) ∧ (p1 → False)) → False) → (((p5 → p6) → (False → False)) ∨ ((True → False) → (p2 → False)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p1 → False) ∧ (p1 → False)) → False) → (((p5 → p6) → (False → False)) ∨ ((True → False) → (p2 → False)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    intro assump_9
    apply False.elim assump_9
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p0 p7 p2 p4 p3 p6 p1 : Prop)
theorem file3_51283 : ((((((True → False) ∧ (p6 ∨ p0)) → ((p7 → False) → False)) ∨ (((p2 ∧ p4) ∧ (p3 ∧ p4)) → ((True → False) → (p1 → p4)))) → False) → False) := by
  intro assump_1
  have assump_32 : ((((True → False) ∧ (p6 ∨ p0)) → ((p7 → False) → False)) ∨ (((p2 ∧ p4) ∧ (p3 ∧ p4)) → ((True → False) → (p1 → p4)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_10
      case inl assump_13 =>
        have assump_33 : True := by
          apply True.intro
        let assump_18 := assump_9 assump_33
        apply False.elim assump_18
      case inr assump_14 =>
        have assump_34 : True := by
          apply True.intro
        let assump_25 := assump_9 assump_34
        apply False.elim assump_25
  let assump_4 := assump_1 assump_32
  apply False.elim assump_4


variable (p5 p3 p4 p7 p0 p6 : Prop)
theorem file3_52183 : (((((False ∨ p4) → False) → False) ∧ (((True → False) → False) → False)) → ((((p0 → p4) ∧ (p4 ∧ p6)) → ((p5 ∨ p7) ∧ (p7 → False))) ∨ (((False → p3) ∧ (p5 ∨ p0)) ∧ ((p6 ∧ p0) ∨ (p0 → False))))) := by
  intro assump_55
  cases assump_55
  case intro assump_56 assump_57 =>
    apply Or.inl
    intro assump_62
    apply And.intro
    cases assump_62
    case intro assump_63 assump_64 =>
      cases assump_64
      case intro assump_67 assump_68 =>
        have assump_115 : ((True → False) → False) := by
          intro assump_77
          have assump_116 : True := by
            apply True.intro
          let assump_80 := assump_77 assump_116
          apply False.elim assump_80
        let assump_76 := assump_57 assump_115
        apply False.elim assump_76
    intro assump_87
    cases assump_62
    case intro assump_90 assump_91 =>
      cases assump_91
      case intro assump_94 assump_95 =>
        have assump_117 : ((True → False) → False) := by
          intro assump_105
          have assump_118 : True := by
            apply True.intro
          let assump_108 := assump_105 assump_118
          apply False.elim assump_108
        let assump_104 := assump_57 assump_117
        apply False.elim assump_104


variable (p7 p6 p4 p3 p1 : Prop)
theorem file3_53468 : ((((((True ∧ True) → False) → ((False → False) ∧ (p3 → p1))) ∨ (((p4 → p6) ∧ (p7 ∨ p3)) → False)) → False) → False) := by
  intro assump_19
  have assump_39 : ((((True ∧ True) → False) → ((False → False) ∧ (p3 → p1))) ∨ (((p4 → p6) ∧ (p7 ∨ p3)) → False)) := by
    apply Or.inl
    intro assump_23
    apply And.intro
    intro assump_24
    apply False.elim assump_24
    intro assump_27
    have assump_40 : (True ∧ True) := by
      apply And.intro
      apply True.intro
      apply True.intro
    let assump_32 := assump_23 assump_40
    apply False.elim assump_32
  let assump_22 := assump_19 assump_39
  apply False.elim assump_22


variable (p5 p1 p0 p3 p2 p4 p7 p6 : Prop)
theorem file3_54172 : ((((((p7 → p3) ∨ (False ∧ p4)) ∧ ((p1 → False) → False)) → (((p5 ∨ False) ∧ (p6 → p7)) → False)) ∧ ((((p7 → False) ∧ (True → True)) ∧ ((p5 → False) ∧ (p7 ∧ False))) ∨ (((p0 ∧ p2) ∧ (p0 → False)) ∧ ((p7 → False) ∧ (p5 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_9
          case intro assump_16 assump_17 =>
            cases assump_17
            case intro assump_20 assump_21 =>
              apply False.elim assump_21
    case inr assump_7 =>
      cases assump_7
      case intro assump_26 assump_27 =>
        cases assump_26
        case intro assump_28 assump_29 =>
          cases assump_28
          case intro assump_30 assump_31 =>
            cases assump_27
            case intro assump_38 assump_39 =>
              have assump_50 : p0 := by
                exact assump_30
              let assump_46 := assump_29 assump_50
              apply False.elim assump_46


variable (p1 p4 p7 p5 p3 p6 : Prop)
theorem file3_55357 : (((((False ∨ True) ∧ (False ∧ p3)) ∧ ((p3 ∨ p4) ∧ (p4 ∨ True))) ∧ (((p6 ∨ p3) ∨ (p1 → p4)) ∧ ((p1 ∧ p1) ∨ (p3 ∨ p6)))) → ((((p6 ∨ p5) ∨ (p7 ∨ False)) → False) ∨ (((p7 → False) → (False → False)) ∧ ((p4 ∨ p1) ∨ (p5 ∧ p5))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          apply False.elim assump_8
        case inr assump_9 =>
          cases assump_7
          case intro assump_14 assump_15 =>
            apply False.elim assump_14


variable (p3 p0 p1 p2 p6 : Prop)
theorem file3_56051 : ((((((p6 ∨ False) → False) → False) → False) ∧ ((((p6 ∧ False) ∧ (p6 → False)) ∨ ((True → False) ∧ (p2 ∧ p6))) ∨ (((p6 ∧ p3) ∨ (p2 ∧ False)) ∧ ((p1 ∨ p2) ∧ (p6 ∨ p0))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            apply False.elim assump_13
      case inr assump_9 =>
        cases assump_9
        case intro assump_18 assump_19 =>
          cases assump_19
          case intro assump_22 assump_23 =>
            have assump_130 : True := by
              apply True.intro
            let assump_30 := assump_18 assump_130
            apply False.elim assump_30
    case inr assump_7 =>
      cases assump_7
      case intro assump_34 assump_35 =>
        cases assump_34
        case inl assump_36 =>
          cases assump_36
          case intro assump_38 assump_39 =>
            cases assump_35
            case intro assump_44 assump_45 =>
              cases assump_44
              case inl assump_46 =>
                cases assump_45
                case inl assump_50 =>
                  have assump_131 : (((p6 ∨ False) → False) → False) := by
                    intro assump_59
                    have assump_132 : (p6 ∨ False) := by
                      apply Or.inl
                      exact assump_50
                    let assump_62 := assump_59 assump_132
                    apply False.elim assump_62
                  let assump_58 := assump_2 assump_131
                  apply False.elim assump_58
                case inr assump_51 =>
                  have assump_133 : (((p6 ∨ False) → False) → False) := by
                    intro assump_76
                    have assump_134 : (p6 ∨ False) := by
                      apply Or.inl
                      exact assump_38
                    let assump_79 := assump_76 assump_134
                    apply False.elim assump_79
                  let assump_75 := assump_2 assump_133
                  apply False.elim assump_75
              case inr assump_47 =>
                cases assump_45
                case inl assump_88 =>
                  have assump_135 : (((p6 ∨ False) → False) → False) := by
                    intro assump_97
                    have assump_136 : (p6 ∨ False) := by
                      apply Or.inl
                      exact assump_88
                    let assump_100 := assump_97 assump_136
                    apply False.elim assump_100
                  let assump_96 := assump_2 assump_135
                  apply False.elim assump_96
                case inr assump_89 =>
                  have assump_137 : (((p6 ∨ False) → False) → False) := by
                    intro assump_114
                    have assump_138 : (p6 ∨ False) := by
                      apply Or.inl
                      exact assump_38
                    let assump_117 := assump_114 assump_138
                    apply False.elim assump_117
                  let assump_113 := assump_2 assump_137
                  apply False.elim assump_113
        case inr assump_37 =>
          cases assump_37
          case intro assump_124 assump_125 =>
            apply False.elim assump_125


variable (p1 p6 p7 p5 p0 p3 : Prop)
theorem file3_59489 : (((((p7 ∨ p1) → (p6 → p5)) ∧ ((p5 ∨ p7) → (p3 → False))) → False) → ((((p7 ∧ p0) ∧ (p7 → False)) → ((p1 ∧ p0) → False)) ∨ (((p7 ∧ p7) → False) → ((False → False) → False)))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_4
    case intro assump_12 assump_13 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        have assump_26 : p7 := by
          exact assump_14
        let assump_22 := assump_13 assump_26
        apply False.elim assump_22


variable (p2 p6 p7 p4 p0 : Prop)
theorem file3_60102 : (((((p0 ∧ p0) → (p7 ∨ False)) ∧ ((True ∨ p2) → False)) → False) ∨ ((((p4 ∨ False) ∨ (p6 → p6)) → False) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_12 : (True ∨ p2) := by
      apply Or.inl
      apply True.intro
    let assump_8 := assump_3 assump_12
    apply False.elim assump_8


variable (p4 p6 p0 p3 p2 p5 p7 p1 : Prop)
theorem file3_60521 : (((((p0 ∨ p1) ∧ (p5 ∨ p4)) ∧ ((p5 ∧ p3) → False)) ∧ (((p3 → False) → (False ∨ p4)) ∨ ((True ∧ p3) → False))) → ((((p2 ∨ p0) ∧ (True → p6)) ∧ ((False ∧ p3) ∧ (True ∧ p7))) → False)) := by
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
          cases assump_13
          case intro assump_15 assump_16 =>
            apply False.elim assump_15
      case inr assump_8 =>
        cases assump_4
        case intro assump_23 assump_24 =>
          cases assump_23
          case intro assump_25 assump_26 =>
            apply False.elim assump_25


variable (p1 p0 p7 p3 p2 p4 : Prop)
theorem file3_61331 : ((((((p2 → p0) ∧ (p3 → p1)) → ((p0 ∧ False) ∨ (p4 ∧ p1))) ∨ (((p1 → False) → False) ∨ ((True ∧ p7) ∨ (p3 ∨ p3)))) ∧ ((((p2 ∧ False) ∧ (p3 ∨ p1)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_101 : (((p2 ∧ False) ∧ (p3 ∨ p1)) → False) := by
        intro assump_11
        cases assump_11
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            apply False.elim assump_15
      let assump_10 := assump_3 assump_101
      apply False.elim assump_10
    case inr assump_5 =>
      cases assump_5
      case inl assump_23 =>
        have assump_102 : (((p2 ∧ False) ∧ (p3 ∨ p1)) → False) := by
          intro assump_30
          cases assump_30
          case intro assump_31 assump_32 =>
            cases assump_31
            case intro assump_33 assump_34 =>
              apply False.elim assump_34
        let assump_29 := assump_3 assump_102
        apply False.elim assump_29
      case inr assump_24 =>
        cases assump_24
        case inl assump_42 =>
          cases assump_42
          case intro assump_44 assump_45 =>
            have assump_103 : (((p2 ∧ False) ∧ (p3 ∨ p1)) → False) := by
              intro assump_53
              cases assump_53
              case intro assump_54 assump_55 =>
                cases assump_54
                case intro assump_56 assump_57 =>
                  apply False.elim assump_57
            let assump_52 := assump_3 assump_103
            apply False.elim assump_52
        case inr assump_43 =>
          cases assump_43
          case inl assump_65 =>
            have assump_104 : (((p2 ∧ False) ∧ (p3 ∨ p1)) → False) := by
              intro assump_72
              cases assump_72
              case intro assump_73 assump_74 =>
                cases assump_73
                case intro assump_75 assump_76 =>
                  apply False.elim assump_76
            let assump_71 := assump_3 assump_104
            apply False.elim assump_71
          case inr assump_66 =>
            have assump_105 : (((p2 ∧ False) ∧ (p3 ∨ p1)) → False) := by
              intro assump_89
              cases assump_89
              case intro assump_90 assump_91 =>
                cases assump_90
                case intro assump_92 assump_93 =>
                  apply False.elim assump_93
            let assump_88 := assump_3 assump_105
            apply False.elim assump_88


variable (p3 p4 p7 p5 p1 : Prop)
theorem file3_63915 : ((((((p4 → False) → (p1 → p1)) → ((p5 ∧ False) → False)) → False) ∧ ((((p7 ∧ True) ∧ (p5 ∨ p3)) ∧ ((p1 ∧ True) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_21 : (((p4 → False) → (p1 → p1)) → ((p5 ∧ False) → False)) := by
      intro assump_10
      intro assump_11
      cases assump_11
      case intro assump_12 assump_13 =>
        apply False.elim assump_13
    let assump_9 := assump_2 assump_21
    apply False.elim assump_9


variable (p0 p4 p7 p1 p3 p2 p5 p6 : Prop)
theorem file3_64486 : ((((((p0 ∧ p5) → (p0 → p7)) → ((p3 ∨ p2) ∨ (p2 → p5))) → False) ∧ ((((p6 ∧ p3) ∧ (True ∨ p2)) ∨ ((p4 ∧ False) → (p5 → False))) ∧ (((p5 ∧ p7) ∧ (p7 ∧ p5)) → ((p6 → p5) ∨ (p1 ∨ p1))))) → False) := by
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
            cases assump_11
            case inl assump_18 =>
              have assump_76 : (((p0 ∧ p5) → (p0 → p7)) → ((p3 ∨ p2) ∨ (p2 → p5))) := by
                intro assump_28
                apply Or.inl
                apply Or.inl
                exact assump_13
              let assump_27 := assump_2 assump_76
              apply False.elim assump_27
            case inr assump_19 =>
              have assump_77 : (((p0 ∧ p5) → (p0 → p7)) → ((p3 ∨ p2) ∨ (p2 → p5))) := by
                intro assump_43
                apply Or.inl
                apply Or.inl
                exact assump_13
              let assump_42 := assump_2 assump_77
              apply False.elim assump_42
      case inr assump_9 =>
        have assump_78 : (((p0 ∧ p5) → (p0 → p7)) → ((p3 ∨ p2) ∨ (p2 → p5))) := by
          intro assump_56
          apply Or.inr
          intro assump_59
          have assump_79 : (((p0 ∧ p5) → (p0 → p7)) → ((p3 ∨ p2) ∨ (p2 → p5))) := by
            intro assump_67
            apply Or.inl
            apply Or.inr
            exact assump_59
          let assump_66 := assump_2 assump_79
          apply False.elim assump_66
        let assump_55 := assump_2 assump_78
        apply False.elim assump_55


variable (p5 p7 p1 p0 : Prop)
theorem file3_66282 : ((((((p7 → False) ∧ (p5 → False)) → ((p0 ∧ p7) ∨ (p5 → False))) ∨ (((True ∧ p7) → (p1 ∧ False)) → False)) → False) → False) := by
  intro assump_1
  have assump_23 : ((((p7 → False) ∧ (p5 → False)) → ((p0 ∧ p7) ∨ (p5 → False))) ∨ (((True ∧ p7) → (p1 ∧ False)) → False)) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inr
      intro assump_12
      have assump_24 : p5 := by
        exact assump_12
      let assump_16 := assump_7 assump_24
      apply False.elim assump_16
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p0 p2 p3 p5 p4 p7 : Prop)
theorem file3_66946 : (((((False → p2) ∨ (p2 → False)) → ((p5 ∨ p7) → False)) → (((p5 ∧ False) → False) ∨ ((p7 → p4) → False))) ∨ ((((p0 ∧ True) ∨ (p3 → p4)) ∨ ((p0 ∨ p4) ∨ (p5 ∧ p5))) → False)) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply False.elim assump_6


variable (p4 p6 p3 p1 p5 p2 p0 p7 : Prop)
theorem file3_67336 : ((((((p2 ∧ p6) → False) ∧ ((p1 → False) → (p6 ∧ p0))) ∧ (((False ∧ p1) ∧ (p1 → False)) ∧ ((p1 → p6) → (p7 → p2)))) ∧ ((((p2 → p0) ∨ (p3 → p5)) ∧ ((False → False) ∨ (p4 ∧ p2))) ∨ (((p1 → True) → False) ∨ ((p4 → False) ∨ (p2 → False))))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        cases assump_9
        case intro assump_16 assump_17 =>
          cases assump_16
          case intro assump_18 assump_19 =>
            cases assump_18
            case intro assump_20 assump_21 =>
              apply False.elim assump_20


variable (p3 p7 p6 p2 p4 : Prop)
theorem file3_68078 : (((((p2 ∨ p6) ∧ (p7 → p3)) ∧ ((False → p7) → False)) ∧ (((False → p4) → False) ∨ ((p4 → p2) ∨ (p2 → False)))) → False) := by
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
          case inl assump_16 =>
            have assump_84 : (False → p4) := by
              intro assump_21
              apply False.elim assump_21
            let assump_20 := assump_16 assump_84
            apply False.elim assump_20
          case inr assump_17 =>
            cases assump_17
            case inl assump_27 =>
              have assump_85 : (False → p7) := by
                intro assump_33
                apply False.elim assump_33
              let assump_32 := assump_5 assump_85
              apply False.elim assump_32
            case inr assump_28 =>
              have assump_86 : p2 := by
                exact assump_8
              let assump_41 := assump_28 assump_86
              apply False.elim assump_41
        case inr assump_9 =>
          cases assump_3
          case inl assump_51 =>
            have assump_87 : (False → p4) := by
              intro assump_56
              apply False.elim assump_56
            let assump_55 := assump_51 assump_87
            apply False.elim assump_55
          case inr assump_52 =>
            cases assump_52
            case inl assump_62 =>
              have assump_88 : (False → p7) := by
                intro assump_68
                apply False.elim assump_68
              let assump_67 := assump_5 assump_88
              apply False.elim assump_67
            case inr assump_63 =>
              have assump_89 : (False → p7) := by
                intro assump_78
                apply False.elim assump_78
              let assump_77 := assump_5 assump_89
              apply False.elim assump_77


variable (p3 p5 p2 p6 p1 : Prop)
theorem file3_70118 : (((((False ∧ p5) → (True → True)) → ((p5 → False) ∧ (True → False))) ∧ (((p6 → p5) ∨ (False → p1)) → False)) → ((((p1 ∧ p5) → (p3 → False)) ∨ ((False → p5) ∧ (p2 ∧ p1))) ∧ (((p3 ∧ False) → (False → False)) ∨ ((p5 ∨ p1) ∧ (p6 ∨ False))))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    intro assump_8
    intro assump_9
    cases assump_8
    case intro assump_12 assump_13 =>
      have assump_38 : ((p6 → p5) ∨ (False → p1)) := by
        apply Or.inl
        intro assump_22
        exact assump_13
      let assump_21 := assump_3 assump_38
      apply False.elim assump_21
  cases assump_1
  case intro assump_28 assump_29 =>
    apply Or.inl
    intro assump_34
    intro assump_35
    apply False.elim assump_35


variable (p6 p1 p5 p0 p4 p7 p2 p3 : Prop)
theorem file3_70967 : (((((p1 ∨ p2) ∧ (p7 ∨ p1)) → ((p6 ∧ p2) ∨ (p0 → False))) → False) → ((((p3 → p5) ∨ (p5 → True)) ∨ ((p7 → p2) ∧ (p1 ∨ p5))) → (((p7 ∨ p0) ∧ (True ∨ p4)) ∨ ((p0 ∨ p5) ∨ (False → p3))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case inl assump_5 =>
      apply Or.inr
      apply Or.inr
      intro assump_11
      apply False.elim assump_11
    case inr assump_6 =>
      apply Or.inr
      apply Or.inr
      intro assump_18
      apply False.elim assump_18
  case inr assump_4 =>
    cases assump_4
    case intro assump_21 assump_22 =>
      cases assump_22
      case inl assump_25 =>
        apply Or.inr
        apply Or.inr
        intro assump_31
        apply False.elim assump_31
      case inr assump_26 =>
        apply Or.inr
        apply Or.inl
        apply Or.inr
        exact assump_26


variable (p7 p3 p1 p4 p0 p5 : Prop)
theorem file3_71892 : ((((((p3 ∧ p7) ∨ (p4 ∧ p5)) → ((True → False) → (p0 → p7))) ∨ (((p7 ∧ p1) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_35 : ((((p3 ∧ p7) ∨ (p4 ∧ p5)) → ((True → False) → (p0 → p7))) ∨ (((p7 ∧ p1) → False) → False)) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_5
    case inl assump_12 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        exact assump_15
    case inr assump_13 =>
      cases assump_13
      case intro assump_20 assump_21 =>
        have assump_36 : True := by
          apply True.intro
        let assump_28 := assump_6 assump_36
        apply False.elim assump_28
  let assump_4 := assump_1 assump_35
  apply False.elim assump_4


variable (p7 p1 p4 p0 p3 : Prop)
theorem file3_72699 : (((((p3 ∨ p4) ∨ (p4 → True)) ∧ ((p7 ∧ p1) → (p0 → p7))) → False) → False) := by
  intro assump_1
  have assump_19 : (((p3 ∨ p4) ∨ (p4 → True)) ∧ ((p7 ∧ p1) → (p0 → p7))) := by
    apply And.intro
    apply Or.inr
    intro assump_5
    apply True.intro
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      exact assump_10
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p0 p3 p2 p6 : Prop)
theorem file3_73188 : (((((p2 ∧ p2) → (False → p6)) ∨ ((False → p3) → (p3 → p0))) → False) → False) := by
  intro assump_1
  have assump_12 : (((p2 ∧ p2) → (False → p6)) ∨ ((False → p3) → (p3 → p0))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    apply False.elim assump_6
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p7 p2 p5 p0 p3 p4 : Prop)
theorem file3_73582 : ((((((p3 → False) → False) → ((p2 → False) → (False → p4))) → (((p7 ∨ True) → False) ∧ ((p5 ∧ p2) → False))) ∧ ((((p0 → p0) → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_22 : (((p0 → p0) → False) → False) := by
      intro assump_9
      have assump_23 : (p0 → p0) := by
        intro assump_13
        exact assump_13
      let assump_12 := assump_9 assump_23
      apply False.elim assump_12
    let assump_8 := assump_3 assump_22
    apply False.elim assump_8


variable (p2 p4 p3 p0 p6 p1 p5 p7 : Prop)
theorem file3_74192 : ((((((p4 → False) ∧ (p3 → False)) → ((p3 → p2) → (p7 ∧ p6))) → (((p6 → p6) → False) ∧ ((p6 ∨ p0) ∧ (p6 → False)))) ∧ ((((p0 ∧ p3) ∧ (p1 → p7)) ∧ ((False ∧ True) ∧ (p4 → p3))) ∧ (((p6 → p5) → (False ∨ p2)) ∨ ((True ∨ True) ∨ (p2 → False))))) → False) := by
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
            cases assump_9
            case intro assump_20 assump_21 =>
              cases assump_20
              case intro assump_22 assump_23 =>
                apply False.elim assump_22


variable (p0 p2 p6 p1 p3 p7 p4 : Prop)
theorem file3_75022 : (((((p4 ∨ True) → False) ∧ ((p1 → p6) ∧ (p3 → True))) ∧ (((p0 ∧ False) → (p2 → False)) → ((p1 → p7) ∧ (p0 → p3)))) → False) := by
  intro assump_14
  cases assump_14
  case intro assump_15 assump_16 =>
    cases assump_15
    case intro assump_17 assump_18 =>
      cases assump_18
      case intro assump_21 assump_22 =>
        have assump_49 : (p4 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_45 := assump_17 assump_49
        apply False.elim assump_45


variable (p5 p6 p3 p2 : Prop)
theorem file3_75571 : (((((False ∨ False) ∧ (p6 ∧ p5)) ∧ ((p2 ∨ p3) → (p6 ∧ p6))) → False) ∨ ((((p3 ∧ p2) ∧ (True ∨ p3)) → ((False → False) → False)) ∨ (((True ∧ p3) ∨ (p5 → False)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        apply False.elim assump_6
      case inr assump_7 =>
        apply False.elim assump_7


variable (p4 p0 p3 p5 p2 : Prop)
theorem file3_76086 : ((((((p4 ∨ p3) → (p2 → p2)) ∨ ((p2 ∨ True) ∨ (p3 → False))) ∨ (((False ∧ p5) → (p4 ∨ p2)) → ((p3 ∧ True) ∧ (p0 ∧ p4)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p4 ∨ p3) → (p2 → p2)) ∨ ((p2 ∨ True) ∨ (p3 → False))) ∨ (((False ∧ p5) → (p4 ∨ p2)) → ((p3 ∧ True) ∧ (p0 ∧ p4)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_5
    case inl assump_9 =>
      exact assump_6
    case inr assump_10 =>
      exact assump_6
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p5 p7 p6 p4 p3 : Prop)
theorem file3_76696 : (((((p6 → False) ∨ (p5 → p3)) ∧ ((p7 → False) ∧ (False ∧ p5))) ∧ (((p3 ∧ p3) ∧ (p3 ∨ p4)) → False)) → False) := by
  intro assump_62
  cases assump_62
  case intro assump_63 assump_64 =>
    cases assump_63
    case intro assump_65 assump_66 =>
      cases assump_65
      case inl assump_67 =>
        cases assump_66
        case intro assump_71 assump_72 =>
          cases assump_72
          case intro assump_75 assump_76 =>
            apply False.elim assump_75
      case inr assump_68 =>
        cases assump_66
        case intro assump_81 assump_82 =>
          cases assump_82
          case intro assump_85 assump_86 =>
            apply False.elim assump_85


variable (p7 p1 p3 p5 : Prop)
theorem file3_77423 : ((((((p5 ∨ p3) ∧ (True → False)) ∧ ((p7 ∨ False) ∧ (p1 → False))) → (((p1 → p3) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_58 : ((((p5 ∨ p3) ∧ (True → False)) ∧ ((p7 ∨ False) ∧ (p1 → False))) → (((p1 → p3) → False) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_11
        case inl assump_13 =>
          cases assump_10
          case intro assump_19 assump_20 =>
            cases assump_19
            case inl assump_21 =>
              have assump_59 : True := by
                apply True.intro
              let assump_29 := assump_12 assump_59
              apply False.elim assump_29
            case inr assump_22 =>
              apply False.elim assump_22
        case inr assump_14 =>
          cases assump_10
          case intro assump_39 assump_40 =>
            cases assump_39
            case inl assump_41 =>
              have assump_60 : True := by
                apply True.intro
              let assump_49 := assump_12 assump_60
              apply False.elim assump_49
            case inr assump_42 =>
              apply False.elim assump_42
  let assump_4 := assump_1 assump_58
  apply False.elim assump_4


variable (p2 p4 p0 p3 p1 : Prop)
theorem file3_78794 : ((((((p4 → False) ∨ (p2 ∨ p3)) ∧ ((False → p4) → (True ∧ p0))) → (((p1 ∧ True) → (True → False)) → ((p1 → False) → (p0 → True)))) ∧ ((((p2 → False) → False) → ((p1 ∨ True) ∨ (p1 → p0))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : (((p2 → False) → False) → ((p1 ∨ True) ∨ (p1 → p0))) := by
      intro assump_9
      apply Or.inl
      apply Or.inr
      apply True.intro
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p3 p4 p0 p6 p7 : Prop)
theorem file3_79361 : (((((p0 → False) → (p7 → False)) ∨ ((p3 → True) → (p6 ∨ True))) ∧ (((p4 ∧ p6) → (True ∨ False)) → False)) → ((((p0 ∨ p4) → False) ∧ ((True → False) → False)) ∨ (((p4 → False) → False) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      apply Or.inl
      apply And.intro
      intro assump_10
      cases assump_10
      case inl assump_11 =>
        have assump_90 : ((p4 ∧ p6) → (True ∨ False)) := by
          intro assump_17
          cases assump_17
          case intro assump_18 assump_19 =>
            apply Or.inl
            apply True.intro
        let assump_16 := assump_3 assump_90
        apply False.elim assump_16
      case inr assump_12 =>
        have assump_91 : ((p4 ∧ p6) → (True ∨ False)) := by
          intro assump_31
          cases assump_31
          case intro assump_32 assump_33 =>
            apply Or.inl
            apply True.intro
        let assump_30 := assump_3 assump_91
        apply False.elim assump_30
      intro assump_41
      have assump_92 : True := by
        apply True.intro
      let assump_44 := assump_41 assump_92
      apply False.elim assump_44
    case inr assump_5 =>
      apply Or.inl
      apply And.intro
      intro assump_52
      cases assump_52
      case inl assump_53 =>
        have assump_93 : ((p4 ∧ p6) → (True ∨ False)) := by
          intro assump_59
          cases assump_59
          case intro assump_60 assump_61 =>
            apply Or.inl
            apply True.intro
        let assump_58 := assump_3 assump_93
        apply False.elim assump_58
      case inr assump_54 =>
        have assump_94 : ((p4 ∧ p6) → (True ∨ False)) := by
          intro assump_73
          cases assump_73
          case intro assump_74 assump_75 =>
            apply Or.inl
            apply True.intro
        let assump_72 := assump_3 assump_94
        apply False.elim assump_72
      intro assump_83
      have assump_95 : True := by
        apply True.intro
      let assump_86 := assump_83 assump_95
      apply False.elim assump_86


variable (p5 p1 p3 p4 p2 p6 p0 : Prop)
theorem file3_81514 : ((((((p3 ∧ p0) ∧ (p6 ∧ p1)) ∨ ((p5 → False) → False)) ∧ (((p5 ∨ p4) ∧ (p0 ∧ True)) ∧ ((p1 ∧ p2) ∧ (p0 ∨ p6)))) ∧ ((((p2 ∨ p5) ∨ (p5 → p5)) → False) ∨ (((False → False) ∧ (True → p0)) → False))) → False) := by
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    cases assump_8
    case intro assump_10 assump_11 =>
      cases assump_10
      case inl assump_12 =>
        cases assump_12
        case intro assump_14 assump_15 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            cases assump_15
            case intro assump_22 assump_23 =>
              cases assump_11
              case intro assump_28 assump_29 =>
                cases assump_28
                case intro assump_30 assump_31 =>
                  cases assump_30
                  case inl assump_32 =>
                    cases assump_31
                    case intro assump_36 assump_37 =>
                      cases assump_29
                      case intro assump_42 assump_43 =>
                        cases assump_42
                        case intro assump_44 assump_45 =>
                          cases assump_43
                          case inl assump_50 =>
                            cases assump_9
                            case inl assump_54 =>
                              have assump_290 : ((p2 ∨ p5) ∨ (p5 → p5)) := by
                                apply Or.inl
                                apply Or.inl
                                exact assump_45
                              let assump_58 := assump_54 assump_290
                              apply False.elim assump_58
                            case inr assump_55 =>
                              have assump_291 : ((False → False) ∧ (True → p0)) := by
                                apply And.intro
                                intro assump_65
                                apply False.elim assump_65
                                intro assump_68
                                exact assump_50
                              let assump_64 := assump_55 assump_291
                              apply False.elim assump_64
                          case inr assump_51 =>
                            cases assump_9
                            case inl assump_76 =>
                              have assump_292 : ((p2 ∨ p5) ∨ (p5 → p5)) := by
                                apply Or.inl
                                apply Or.inl
                                exact assump_45
                              let assump_80 := assump_76 assump_292
                              apply False.elim assump_80
                            case inr assump_77 =>
                              have assump_293 : ((False → False) ∧ (True → p0)) := by
                                apply And.intro
                                intro assump_87
                                apply False.elim assump_87
                                intro assump_90
                                exact assump_36
                              let assump_86 := assump_77 assump_293
                              apply False.elim assump_86
                  case inr assump_33 =>
                    cases assump_31
                    case intro assump_98 assump_99 =>
                      cases assump_29
                      case intro assump_104 assump_105 =>
                        cases assump_104
                        case intro assump_106 assump_107 =>
                          cases assump_105
                          case inl assump_112 =>
                            cases assump_9
                            case inl assump_116 =>
                              have assump_294 : ((p2 ∨ p5) ∨ (p5 → p5)) := by
                                apply Or.inl
                                apply Or.inl
                                exact assump_107
                              let assump_120 := assump_116 assump_294
                              apply False.elim assump_120
                            case inr assump_117 =>
                              have assump_295 : ((False → False) ∧ (True → p0)) := by
                                apply And.intro
                                intro assump_127
                                apply False.elim assump_127
                                intro assump_130
                                exact assump_112
                              let assump_126 := assump_117 assump_295
                              apply False.elim assump_126
                          case inr assump_113 =>
                            cases assump_9
                            case inl assump_138 =>
                              have assump_296 : ((p2 ∨ p5) ∨ (p5 → p5)) := by
                                apply Or.inl
                                apply Or.inl
                                exact assump_107
                              let assump_142 := assump_138 assump_296
                              apply False.elim assump_142
                            case inr assump_139 =>
                              have assump_297 : ((False → False) ∧ (True → p0)) := by
                                apply And.intro
                                intro assump_149
                                apply False.elim assump_149
                                intro assump_152
                                exact assump_98
                              let assump_148 := assump_139 assump_297
                              apply False.elim assump_148
      case inr assump_13 =>
        cases assump_11
        case intro assump_160 assump_161 =>
          cases assump_160
          case intro assump_162 assump_163 =>
            cases assump_162
            case inl assump_164 =>
              cases assump_163
              case intro assump_168 assump_169 =>
                cases assump_161
                case intro assump_174 assump_175 =>
                  cases assump_174
                  case intro assump_176 assump_177 =>
                    cases assump_175
                    case inl assump_182 =>
                      cases assump_9
                      case inl assump_186 =>
                        have assump_298 : ((p2 ∨ p5) ∨ (p5 → p5)) := by
                          apply Or.inl
                          apply Or.inl
                          exact assump_177
                        let assump_190 := assump_186 assump_298
                        apply False.elim assump_190
                      case inr assump_187 =>
                        have assump_299 : ((False → False) ∧ (True → p0)) := by
                          apply And.intro
                          intro assump_197
                          apply False.elim assump_197
                          intro assump_200
                          exact assump_182
                        let assump_196 := assump_187 assump_299
                        apply False.elim assump_196
                    case inr assump_183 =>
                      cases assump_9
                      case inl assump_208 =>
                        have assump_300 : ((p2 ∨ p5) ∨ (p5 → p5)) := by
                          apply Or.inl
                          apply Or.inl
                          exact assump_177
                        let assump_212 := assump_208 assump_300
                        apply False.elim assump_212
                      case inr assump_209 =>
                        have assump_301 : ((False → False) ∧ (True → p0)) := by
                          apply And.intro
                          intro assump_219
                          apply False.elim assump_219
                          intro assump_222
                          exact assump_168
                        let assump_218 := assump_209 assump_301
                        apply False.elim assump_218
            case inr assump_165 =>
              cases assump_163
              case intro assump_230 assump_231 =>
                cases assump_161
                case intro assump_236 assump_237 =>
                  cases assump_236
                  case intro assump_238 assump_239 =>
                    cases assump_237
                    case inl assump_244 =>
                      cases assump_9
                      case inl assump_248 =>
                        have assump_302 : ((p2 ∨ p5) ∨ (p5 → p5)) := by
                          apply Or.inl
                          apply Or.inl
                          exact assump_239
                        let assump_252 := assump_248 assump_302
                        apply False.elim assump_252
                      case inr assump_249 =>
                        have assump_303 : ((False → False) ∧ (True → p0)) := by
                          apply And.intro
                          intro assump_259
                          apply False.elim assump_259
                          intro assump_262
                          exact assump_244
                        let assump_258 := assump_249 assump_303
                        apply False.elim assump_258
                    case inr assump_245 =>
                      cases assump_9
                      case inl assump_270 =>
                        have assump_304 : ((p2 ∨ p5) ∨ (p5 → p5)) := by
                          apply Or.inl
                          apply Or.inl
                          exact assump_239
                        let assump_274 := assump_270 assump_304
                        apply False.elim assump_274
                      case inr assump_271 =>
                        have assump_305 : ((False → False) ∧ (True → p0)) := by
                          apply And.intro
                          intro assump_281
                          apply False.elim assump_281
                          intro assump_284
                          exact assump_230
                        let assump_280 := assump_271 assump_305
                        apply False.elim assump_280


variable (p3 p7 p1 p6 p2 p0 p4 : Prop)
theorem file3_91554 : (((((p6 → False) → False) ∨ ((p2 ∧ p2) → (p2 → False))) → (((p4 → p1) ∨ (p3 ∧ p2)) → ((False → False) ∨ (p0 ∨ p0)))) ∨ ((((True → p1) ∧ (p2 ∧ p6)) → ((p7 → p0) → (p6 → p2))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case inl assump_7 =>
      apply Or.inl
      intro assump_11
      apply False.elim assump_11
    case inr assump_8 =>
      apply Or.inl
      intro assump_16
      apply False.elim assump_16
  case inr assump_4 =>
    cases assump_4
    case intro assump_19 assump_20 =>
      cases assump_1
      case inl assump_25 =>
        apply Or.inl
        intro assump_29
        apply False.elim assump_29
      case inr assump_26 =>
        apply Or.inl
        intro assump_34
        apply False.elim assump_34


variable (p0 p4 p3 p1 p5 p6 : Prop)
theorem file3_92427 : (((((p1 → p5) → (p3 → False)) ∨ ((p3 → False) ∨ (p5 ∨ p0))) ∧ (((False ∧ p4) → (p6 ∧ p3)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_78 : ((False ∧ p4) → (p6 ∧ p3)) := by
        intro assump_11
        apply And.intro
        cases assump_11
        case intro assump_12 assump_13 =>
          apply False.elim assump_12
        cases assump_11
        case intro assump_16 assump_17 =>
          apply False.elim assump_16
      let assump_10 := assump_3 assump_78
      apply False.elim assump_10
    case inr assump_5 =>
      cases assump_5
      case inl assump_23 =>
        have assump_79 : ((False ∧ p4) → (p6 ∧ p3)) := by
          intro assump_30
          apply And.intro
          cases assump_30
          case intro assump_31 assump_32 =>
            apply False.elim assump_31
          cases assump_30
          case intro assump_35 assump_36 =>
            apply False.elim assump_35
        let assump_29 := assump_3 assump_79
        apply False.elim assump_29
      case inr assump_24 =>
        cases assump_24
        case inl assump_42 =>
          have assump_80 : ((False ∧ p4) → (p6 ∧ p3)) := by
            intro assump_49
            apply And.intro
            cases assump_49
            case intro assump_50 assump_51 =>
              apply False.elim assump_50
            cases assump_49
            case intro assump_54 assump_55 =>
              apply False.elim assump_54
          let assump_48 := assump_3 assump_80
          apply False.elim assump_48
        case inr assump_43 =>
          have assump_81 : ((False ∧ p4) → (p6 ∧ p3)) := by
            intro assump_66
            apply And.intro
            cases assump_66
            case intro assump_67 assump_68 =>
              apply False.elim assump_67
            cases assump_66
            case intro assump_71 assump_72 =>
              apply False.elim assump_71
          let assump_65 := assump_3 assump_81
          apply False.elim assump_65


variable (p0 p6 p2 p5 : Prop)
theorem file3_94544 : (((((p5 ∨ p6) ∧ (p0 ∧ p5)) ∨ ((False ∨ p2) ∨ (False → False))) → False) → False) := by
  intro assump_1
  have assump_11 : (((p5 ∨ p6) ∧ (p0 ∧ p5)) ∨ ((False ∨ p2) ∨ (False → False))) := by
    apply Or.inr
    apply Or.inr
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p4 p2 p6 p0 p7 p3 p5 p1 : Prop)
theorem file3_94948 : (((((p6 → p0) ∧ (p1 ∨ p6)) ∧ ((p3 ∨ p5) → False)) → (((p5 ∧ False) ∨ (p1 ∨ p4)) ∨ ((p0 ∧ True) → False))) → ((((True ∨ False) ∧ (True → False)) → ((p2 ∧ p7) → False)) ∨ (((p5 ∨ False) ∨ (p3 → False)) ∨ ((p5 → p5) → False)))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_4
    case intro assump_12 assump_13 =>
      cases assump_12
      case inl assump_14 =>
        have assump_26 : True := by
          apply True.intro
        let assump_20 := assump_13 assump_26
        apply False.elim assump_20
      case inr assump_15 =>
        apply False.elim assump_15


variable (p1 p7 p3 p0 p4 p6 p2 p5 : Prop)
theorem file3_95675 : (((((p2 → p5) ∧ (p6 ∨ p1)) → ((p1 → False) ∨ (p6 → p7))) ∧ (((p6 → False) → (False ∨ True)) → False)) → ((((p1 ∨ p7) → False) ∨ ((p2 → p6) ∨ (p6 → p0))) ∧ (((p3 ∨ p6) ∧ (p4 → p4)) ∧ ((False ∨ False) → False)))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    intro assump_8
    cases assump_8
    case inl assump_9 =>
      have assump_60 : ((p6 → False) → (False ∨ True)) := by
        intro assump_15
        apply Or.inr
        apply True.intro
      let assump_14 := assump_3 assump_60
      apply False.elim assump_14
    case inr assump_10 =>
      have assump_61 : ((p6 → False) → (False ∨ True)) := by
        intro assump_25
        apply Or.inr
        apply True.intro
      let assump_24 := assump_3 assump_61
      apply False.elim assump_24
  apply And.intro
  apply And.intro
  cases assump_1
  case intro assump_31 assump_32 =>
    have assump_62 : ((p6 → False) → (False ∨ True)) := by
      intro assump_38
      apply Or.inr
      apply True.intro
    let assump_37 := assump_32 assump_62
    apply False.elim assump_37
  intro assump_44
  cases assump_1
  case intro assump_47 assump_48 =>
    exact assump_44
  intro assump_53
  cases assump_53
  case inl assump_54 =>
    apply False.elim assump_54
  case inr assump_55 =>
    apply False.elim assump_55


variable (p3 p4 p6 p7 p2 p5 p1 p0 : Prop)
theorem file3_97083 : (((((True → False) → False) ∧ ((p4 ∨ p5) → False)) ∨ (((p4 → p5) ∧ (p4 ∧ p3)) ∨ ((p6 ∨ True) ∨ (p4 ∨ p2)))) → ((((p6 → True) → False) → False) ∨ (((p7 ∧ p5) → False) ∨ ((p0 ∨ p1) → False)))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply Or.inl
      intro assump_10
      have assump_84 : (p6 → True) := by
        intro assump_14
        apply True.intro
      let assump_13 := assump_10 assump_84
      apply False.elim assump_13
  case inr assump_3 =>
    cases assump_3
    case inl assump_18 =>
      cases assump_18
      case intro assump_20 assump_21 =>
        cases assump_21
        case intro assump_24 assump_25 =>
          apply Or.inl
          intro assump_30
          have assump_85 : (p6 → True) := by
            intro assump_34
            apply True.intro
          let assump_33 := assump_30 assump_85
          apply False.elim assump_33
    case inr assump_19 =>
      cases assump_19
      case inl assump_38 =>
        cases assump_38
        case inl assump_40 =>
          apply Or.inl
          intro assump_44
          have assump_86 : (p6 → True) := by
            intro assump_48
            apply True.intro
          let assump_47 := assump_44 assump_86
          apply False.elim assump_47
        case inr assump_41 =>
          apply Or.inl
          intro assump_54
          have assump_87 : (p6 → True) := by
            intro assump_58
            apply True.intro
          let assump_57 := assump_54 assump_87
          apply False.elim assump_57
      case inr assump_39 =>
        cases assump_39
        case inl assump_62 =>
          apply Or.inl
          intro assump_66
          have assump_88 : (p6 → True) := by
            intro assump_70
            apply True.intro
          let assump_69 := assump_66 assump_88
          apply False.elim assump_69
        case inr assump_63 =>
          apply Or.inl
          intro assump_76
          have assump_89 : (p6 → True) := by
            intro assump_80
            apply True.intro
          let assump_79 := assump_76 assump_89
          apply False.elim assump_79


variable (p1 p7 : Prop)
theorem file3_99290 : (((((p1 ∨ p1) ∨ (True ∧ True)) ∨ ((False → p1) → (p7 → False))) → False) → False) := by
  intro assump_1
  have assump_8 : (((p1 ∨ p1) ∨ (True ∧ True)) ∨ ((False → p1) → (p7 → False))) := by
    apply Or.inl
    apply Or.inr
    apply And.intro
    apply True.intro
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p4 p3 p0 p2 p7 p5 : Prop)
theorem file3_99701 : (((((True → False) ∨ (p5 → False)) → ((p7 → False) → (p5 ∨ True))) ∨ (((p3 → True) ∧ (True → True)) → False)) ∨ ((((p2 → False) → (True ∨ True)) ∧ ((p0 → False) → False)) → (((p7 → p5) → (p4 → False)) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_36
  intro assump_37
  cases assump_36
  case inl assump_40 =>
    apply Or.inr
    apply True.intro
  case inr assump_41 =>
    apply Or.inr
    apply True.intro


variable (p7 p1 p6 p2 p0 p4 p3 : Prop)
theorem file3_100190 : ((((((p6 → False) ∧ (p6 ∨ False)) → ((p3 → p4) → (p0 ∨ p7))) → False) ∨ ((((False → False) ∨ (p0 → p2)) ∨ ((p0 → p2) ∨ (p1 → p0))) → (((False ∧ True) → False) ∧ ((False → False) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_44 : (((p6 → False) ∧ (p6 ∨ False)) → ((p3 → p4) → (p0 ∨ p7))) := by
      intro assump_7
      intro assump_8
      cases assump_7
      case intro assump_11 assump_12 =>
        cases assump_12
        case inl assump_15 =>
          have assump_45 : p6 := by
            exact assump_15
          let assump_20 := assump_11 assump_45
          apply False.elim assump_20
        case inr assump_16 =>
          apply False.elim assump_16
    let assump_6 := assump_2 assump_44
    apply False.elim assump_6
  case inr assump_3 =>
    have assump_46 : (((False → False) ∨ (p0 → p2)) ∨ ((p0 → p2) ∨ (p1 → p0))) := by
      apply Or.inl
      apply Or.inl
      intro assump_32
      apply False.elim assump_32
    let assump_31 := assump_3 assump_46
    let assump_35 := And.right assump_31
    have assump_47 : (False → False) := by
      intro assump_38
      apply False.elim assump_38
    let assump_37 := assump_35 assump_47
    apply False.elim assump_37


variable (p0 p5 p3 p6 p7 p4 p2 : Prop)
theorem file3_101493 : (((((p4 ∧ p6) ∧ (False → False)) → False) → (((p0 → p7) → (p2 → False)) ∧ ((p7 ∧ p2) ∧ (p2 ∨ True)))) → ((((True ∨ p0) → (False ∧ p4)) → ((p5 ∧ p7) ∨ (p2 ∨ p7))) ∨ (((p5 ∨ p3) → False) → False))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_12 : (True ∨ p0) := by
    apply Or.inl
    apply True.intro
  let assump_7 := assump_4 assump_12
  let assump_8 := And.left assump_7
  apply False.elim assump_8


variable (p2 p7 p3 : Prop)
theorem file3_101971 : (((((True → False) ∧ (True ∨ False)) → ((p2 ∨ True) ∨ (p3 ∧ p7))) → False) → False) := by
  intro assump_12
  have assump_30 : (((True → False) ∧ (True ∨ False)) → ((p2 ∨ True) ∨ (p3 ∧ p7))) := by
    intro assump_16
    cases assump_16
    case intro assump_17 assump_18 =>
      cases assump_18
      case inl assump_21 =>
        apply Or.inl
        apply Or.inr
        apply True.intro
      case inr assump_22 =>
        apply False.elim assump_22
  let assump_15 := assump_12 assump_30
  apply False.elim assump_15


variable (p3 p0 p4 p7 p6 p2 : Prop)
theorem file3_102554 : ((((((p7 ∧ p4) → False) → ((p7 ∧ False) → False)) ∨ (((False → p2) → (p3 → p2)) → ((p7 → p6) → (p0 ∨ p6)))) → False) → False) := by
  intro assump_1
  have assump_16 : ((((p7 ∧ p4) → False) → ((p7 ∧ False) → False)) ∨ (((False → p2) → (p3 → p2)) → ((p7 → p6) → (p0 ∨ p6)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_8
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p7 p5 p4 p2 p0 p6 p1 : Prop)
theorem file3_103104 : (((((p7 → False) → (p7 ∨ p2)) ∧ ((p1 → p5) ∨ (p7 → False))) ∧ (((p5 ∨ True) → False) ∧ ((p2 → False) ∨ (p4 → False)))) → ((((False ∧ p4) ∨ (True → False)) → ((p7 ∧ p0) ∧ (p1 → p2))) ∧ (((True → p5) ∨ (False → p6)) → False))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  apply And.intro
  apply And.intro
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      apply False.elim assump_5
  case inr assump_4 =>
    cases assump_1
    case intro assump_11 assump_12 =>
      cases assump_11
      case intro assump_13 assump_14 =>
        cases assump_14
        case inl assump_17 =>
          cases assump_12
          case intro assump_21 assump_22 =>
            cases assump_22
            case inl assump_25 =>
              have assump_297 : (p5 ∨ True) := by
                apply Or.inr
                apply True.intro
              let assump_30 := assump_21 assump_297
              apply False.elim assump_30
            case inr assump_26 =>
              have assump_298 : (p5 ∨ True) := by
                apply Or.inr
                apply True.intro
              let assump_37 := assump_21 assump_298
              apply False.elim assump_37
        case inr assump_18 =>
          cases assump_12
          case intro assump_43 assump_44 =>
            cases assump_44
            case inl assump_47 =>
              have assump_299 : (p5 ∨ True) := by
                apply Or.inr
                apply True.intro
              let assump_52 := assump_43 assump_299
              apply False.elim assump_52
            case inr assump_48 =>
              have assump_300 : (p5 ∨ True) := by
                apply Or.inr
                apply True.intro
              let assump_59 := assump_43 assump_300
              apply False.elim assump_59
  cases assump_2
  case inl assump_63 =>
    cases assump_63
    case intro assump_65 assump_66 =>
      apply False.elim assump_65
  case inr assump_64 =>
    cases assump_1
    case intro assump_71 assump_72 =>
      cases assump_71
      case intro assump_73 assump_74 =>
        cases assump_74
        case inl assump_77 =>
          cases assump_72
          case intro assump_81 assump_82 =>
            cases assump_82
            case inl assump_85 =>
              have assump_301 : (p5 ∨ True) := by
                apply Or.inr
                apply True.intro
              let assump_90 := assump_81 assump_301
              apply False.elim assump_90
            case inr assump_86 =>
              have assump_302 : (p5 ∨ True) := by
                apply Or.inr
                apply True.intro
              let assump_97 := assump_81 assump_302
              apply False.elim assump_97
        case inr assump_78 =>
          cases assump_72
          case intro assump_103 assump_104 =>
            cases assump_104
            case inl assump_107 =>
              have assump_303 : (p5 ∨ True) := by
                apply Or.inr
                apply True.intro
              let assump_112 := assump_103 assump_303
              apply False.elim assump_112
            case inr assump_108 =>
              have assump_304 : (p5 ∨ True) := by
                apply Or.inr
                apply True.intro
              let assump_119 := assump_103 assump_304
              apply False.elim assump_119
  intro assump_123
  cases assump_2
  case inl assump_126 =>
    cases assump_126
    case intro assump_128 assump_129 =>
      apply False.elim assump_128
  case inr assump_127 =>
    cases assump_1
    case intro assump_134 assump_135 =>
      cases assump_134
      case intro assump_136 assump_137 =>
        cases assump_137
        case inl assump_140 =>
          cases assump_135
          case intro assump_144 assump_145 =>
            cases assump_145
            case inl assump_148 =>
              have assump_305 : (p5 ∨ True) := by
                apply Or.inr
                apply True.intro
              let assump_153 := assump_144 assump_305
              apply False.elim assump_153
            case inr assump_149 =>
              have assump_306 : (p5 ∨ True) := by
                apply Or.inr
                apply True.intro
              let assump_160 := assump_144 assump_306
              apply False.elim assump_160
        case inr assump_141 =>
          cases assump_135
          case intro assump_166 assump_167 =>
            cases assump_167
            case inl assump_170 =>
              have assump_307 : (p5 ∨ True) := by
                apply Or.inr
                apply True.intro
              let assump_175 := assump_166 assump_307
              apply False.elim assump_175
            case inr assump_171 =>
              have assump_308 : (p5 ∨ True) := by
                apply Or.inr
                apply True.intro
              let assump_182 := assump_166 assump_308
              apply False.elim assump_182
  intro assump_186
  cases assump_186
  case inl assump_187 =>
    cases assump_1
    case intro assump_191 assump_192 =>
      cases assump_191
      case intro assump_193 assump_194 =>
        cases assump_194
        case inl assump_197 =>
          cases assump_192
          case intro assump_201 assump_202 =>
            cases assump_202
            case inl assump_205 =>
              have assump_309 : (p5 ∨ True) := by
                apply Or.inr
                apply True.intro
              let assump_210 := assump_201 assump_309
              apply False.elim assump_210
            case inr assump_206 =>
              have assump_310 : (p5 ∨ True) := by
                apply Or.inr
                apply True.intro
              let assump_217 := assump_201 assump_310
              apply False.elim assump_217
        case inr assump_198 =>
          cases assump_192
          case intro assump_223 assump_224 =>
            cases assump_224
            case inl assump_227 =>
              have assump_311 : (p5 ∨ True) := by
                apply Or.inr
                apply True.intro
              let assump_232 := assump_223 assump_311
              apply False.elim assump_232
            case inr assump_228 =>
              have assump_312 : (p5 ∨ True) := by
                apply Or.inr
                apply True.intro
              let assump_239 := assump_223 assump_312
              apply False.elim assump_239
  case inr assump_188 =>
    cases assump_1
    case intro assump_245 assump_246 =>
      cases assump_245
      case intro assump_247 assump_248 =>
        cases assump_248
        case inl assump_251 =>
          cases assump_246
          case intro assump_255 assump_256 =>
            cases assump_256
            case inl assump_259 =>
              have assump_313 : (p5 ∨ True) := by
                apply Or.inr
                apply True.intro
              let assump_264 := assump_255 assump_313
              apply False.elim assump_264
            case inr assump_260 =>
              have assump_314 : (p5 ∨ True) := by
                apply Or.inr
                apply True.intro
              let assump_271 := assump_255 assump_314
              apply False.elim assump_271
        case inr assump_252 =>
          cases assump_246
          case intro assump_277 assump_278 =>
            cases assump_278
            case inl assump_281 =>
              have assump_315 : (p5 ∨ True) := by
                apply Or.inr
                apply True.intro
              let assump_286 := assump_277 assump_315
              apply False.elim assump_286
            case inr assump_282 =>
              have assump_316 : (p5 ∨ True) := by
                apply Or.inr
                apply True.intro
              let assump_293 := assump_277 assump_316
              apply False.elim assump_293


variable (p4 p5 p2 p6 p3 p1 p0 p7 : Prop)
theorem file3_110946 : (((((False ∨ p6) ∧ (p5 ∧ p4)) ∧ ((p0 → p6) → (p4 → False))) → (((p5 ∧ p7) ∧ (p5 ∨ p3)) → ((p7 → False) ∨ (p3 ∧ p0)))) ∨ ((((p7 ∨ p5) → False) ∧ ((p2 → True) → (p7 → False))) → (((True ∧ p2) → False) ∨ ((True ∧ p4) → (p1 ∧ False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_4
      case inl assump_11 =>
        cases assump_1
        case intro assump_15 assump_16 =>
          cases assump_15
          case intro assump_17 assump_18 =>
            cases assump_17
            case inl assump_19 =>
              apply False.elim assump_19
            case inr assump_20 =>
              cases assump_18
              case intro assump_25 assump_26 =>
                apply Or.inl
                intro assump_33
                have assump_77 : (p0 → p6) := by
                  intro assump_38
                  exact assump_20
                let assump_37 := assump_16 assump_77
                have assump_78 : p4 := by
                  exact assump_26
                let assump_41 := assump_37 assump_78
                apply False.elim assump_41
      case inr assump_12 =>
        cases assump_1
        case intro assump_47 assump_48 =>
          cases assump_47
          case intro assump_49 assump_50 =>
            cases assump_49
            case inl assump_51 =>
              apply False.elim assump_51
            case inr assump_52 =>
              cases assump_50
              case intro assump_57 assump_58 =>
                apply Or.inl
                intro assump_65
                have assump_79 : (p0 → p6) := by
                  intro assump_70
                  exact assump_52
                let assump_69 := assump_48 assump_79
                have assump_80 : p4 := by
                  exact assump_58
                let assump_73 := assump_69 assump_80
                apply False.elim assump_73


variable (p0 p6 p1 p2 : Prop)
theorem file3_112977 : (((((p0 → p6) → (p2 → p2)) ∨ ((p1 → False) → (p6 → False))) → False) → False) := by
  intro assump_1
  have assump_14 : (((p0 → p6) → (p2 → p2)) ∨ ((p1 → False) → (p6 → False))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    exact assump_6
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p5 p4 p2 p6 p3 : Prop)
theorem file3_113357 : (((((p4 ∧ p4) ∨ (True ∨ p6)) ∧ ((p3 ∧ False) → (True ∨ p5))) ∨ (((p2 → True) ∧ (p6 → True)) ∧ ((p2 ∧ p3) ∧ (False ∧ True)))) ∨ ((((p3 ∧ p2) → False) → ((True → p4) → False)) ∧ (((p6 ∨ p2) → (p4 → False)) ∨ ((False → False) → False)))) := by
  apply Or.inl
  apply Or.inl
  apply And.intro
  apply Or.inr
  apply Or.inl
  apply True.intro
  intro assump_31
  cases assump_31
  case intro assump_32 assump_33 =>
    apply False.elim assump_33


variable (p7 p3 p1 p6 p0 p5 p2 : Prop)
theorem file3_113861 : ((((((p7 ∨ p2) ∨ (p7 → False)) → False) ∨ (((p2 ∧ p1) ∨ (False → p3)) → ((p1 ∨ p3) ∧ (p1 → False)))) ∧ ((((p5 → p1) ∧ (p3 ∧ p1)) → False) ∧ (((p2 → p6) ∨ (p3 → p5)) ∧ ((True → False) ∧ (p0 → False))))) → False) := by
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
          case inl assump_14 =>
            cases assump_13
            case intro assump_18 assump_19 =>
              have assump_78 : True := by
                apply True.intro
              let assump_25 := assump_18 assump_78
              apply False.elim assump_25
          case inr assump_15 =>
            cases assump_13
            case intro assump_31 assump_32 =>
              have assump_79 : True := by
                apply True.intro
              let assump_38 := assump_31 assump_79
              apply False.elim assump_38
    case inr assump_5 =>
      cases assump_3
      case intro assump_44 assump_45 =>
        cases assump_45
        case intro assump_48 assump_49 =>
          cases assump_48
          case inl assump_50 =>
            cases assump_49
            case intro assump_54 assump_55 =>
              have assump_80 : True := by
                apply True.intro
              let assump_61 := assump_54 assump_80
              apply False.elim assump_61
          case inr assump_51 =>
            cases assump_49
            case intro assump_67 assump_68 =>
              have assump_81 : True := by
                apply True.intro
              let assump_74 := assump_67 assump_81
              apply False.elim assump_74


variable (p6 p7 p5 p0 p2 p4 p1 p3 : Prop)
theorem file3_115676 : (((((True ∨ p3) ∧ (p7 → p7)) ∨ ((p6 ∨ p6) ∨ (p7 → False))) → False) → ((((True ∨ True) ∧ (True ∨ False)) ∧ ((p0 → p4) ∧ (False ∧ True))) → (((p3 → p1) ∨ (p1 ∨ p2)) ∧ ((p0 ∧ p7) ∨ (p2 ∨ p5))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case inl assump_7 =>
        cases assump_6
        case inl assump_11 =>
          cases assump_4
          case intro assump_15 assump_16 =>
            cases assump_16
            case intro assump_19 assump_20 =>
              apply False.elim assump_19
        case inr assump_12 =>
          apply False.elim assump_12
      case inr assump_8 =>
        cases assump_6
        case inl assump_27 =>
          cases assump_4
          case intro assump_31 assump_32 =>
            cases assump_32
            case intro assump_35 assump_36 =>
              apply False.elim assump_35
        case inr assump_28 =>
          apply False.elim assump_28
  cases assump_2
  case intro assump_41 assump_42 =>
    cases assump_41
    case intro assump_43 assump_44 =>
      cases assump_43
      case inl assump_45 =>
        cases assump_44
        case inl assump_49 =>
          cases assump_42
          case intro assump_53 assump_54 =>
            cases assump_54
            case intro assump_57 assump_58 =>
              apply False.elim assump_57
        case inr assump_50 =>
          apply False.elim assump_50
      case inr assump_46 =>
        cases assump_44
        case inl assump_65 =>
          cases assump_42
          case intro assump_69 assump_70 =>
            cases assump_70
            case intro assump_73 assump_74 =>
              apply False.elim assump_73
        case inr assump_66 =>
          apply False.elim assump_66


variable (p3 p7 p5 p1 p2 : Prop)
theorem file3_117574 : ((((((p2 ∧ p5) → (True ∨ True)) → ((p3 ∧ p5) → (p7 → p1))) → False) ∧ ((((False → False) → False) → ((p3 ∨ p5) → (p5 ∨ p2))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_31 : (((False → False) → False) → ((p3 ∨ p5) → (p5 ∨ p2))) := by
      intro assump_9
      intro assump_10
      cases assump_10
      case inl assump_11 =>
        have assump_32 : (False → False) := by
          intro assump_18
          apply False.elim assump_18
        let assump_17 := assump_9 assump_32
        apply False.elim assump_17
      case inr assump_12 =>
        apply Or.inl
        exact assump_12
    let assump_8 := assump_3 assump_31
    apply False.elim assump_8


variable (p2 p6 p3 p1 p0 p5 p4 : Prop)
theorem file3_118360 : (((((True → False) → (p2 ∨ p6)) → False) ∧ (((p5 ∧ False) ∧ (False ∨ True)) → False)) → ((((True → False) → (p2 ∧ p3)) ∧ ((p4 ∧ True) → False)) → (((p1 ∨ True) ∨ (True → False)) ∧ ((p3 → False) ∧ (p0 → p0))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_1
    case intro assump_9 assump_10 =>
      apply Or.inl
      apply Or.inr
      apply True.intro
  apply And.intro
  intro assump_15
  cases assump_2
  case intro assump_18 assump_19 =>
    cases assump_1
    case intro assump_24 assump_25 =>
      have assump_57 : ((True → False) → (p2 ∨ p6)) := by
        intro assump_32
        have assump_58 : True := by
          apply True.intro
        let assump_35 := assump_32 assump_58
        apply False.elim assump_35
      let assump_31 := assump_24 assump_57
      apply False.elim assump_31
  intro assump_42
  cases assump_2
  case intro assump_45 assump_46 =>
    cases assump_1
    case intro assump_51 assump_52 =>
      exact assump_42


variable (p7 p0 p1 p2 p4 p5 p3 : Prop)
theorem file3_119456 : ((((((p3 ∨ p4) ∨ (p5 ∨ p1)) ∨ ((True ∧ True) ∨ (p2 → p5))) ∨ (((p0 ∨ p5) ∨ (True ∧ p2)) ∧ ((p4 ∧ p7) ∧ (True → False)))) → False) → False) := by
  intro assump_1
  have assump_8 : ((((p3 ∨ p4) ∨ (p5 ∨ p1)) ∨ ((True ∧ True) ∨ (p2 → p5))) ∨ (((p0 ∨ p5) ∨ (True ∧ p2)) ∧ ((p4 ∧ p7) ∧ (True → False)))) := by
    apply Or.inl
    apply Or.inr
    apply Or.inl
    apply And.intro
    apply True.intro
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p1 p6 p4 p3 p2 p0 p7 : Prop)
theorem file3_120001 : (((((p1 ∨ p7) → False) ∧ ((p0 ∧ p1) → (p3 → False))) → (((p7 ∧ p4) ∧ (True ∨ p2)) → False)) → ((((p3 → True) ∧ (p4 ∧ p4)) → ((p0 → p0) → (p4 ∨ False))) ∨ (((p0 → p6) → False) ∨ ((True → False) → False)))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_4
  case intro assump_8 assump_9 =>
    cases assump_9
    case intro assump_12 assump_13 =>
      apply Or.inl
      exact assump_13


variable (p5 p0 p3 p4 p7 p2 p1 : Prop)
theorem file3_120490 : (((((p2 → False) ∨ (p0 → p0)) ∧ ((p5 ∨ True) ∨ (p7 ∧ p2))) → (((False → False) → False) → ((p4 ∨ True) → (p3 → False)))) ∨ ((((p2 → False) ∧ (p5 ∧ p3)) ∨ ((False → False) → (p1 → False))) → (((p1 → False) → (p1 → False)) ∧ ((p4 ∧ p5) ∨ (p2 → p1))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_3
  case inl assump_7 =>
    cases assump_1
    case intro assump_13 assump_14 =>
      cases assump_13
      case inl assump_15 =>
        cases assump_14
        case inl assump_19 =>
          cases assump_19
          case inl assump_21 =>
            have assump_189 : (False → False) := by
              intro assump_28
              apply False.elim assump_28
            let assump_27 := assump_2 assump_189
            apply False.elim assump_27
          case inr assump_22 =>
            have assump_190 : (False → False) := by
              intro assump_38
              apply False.elim assump_38
            let assump_37 := assump_2 assump_190
            apply False.elim assump_37
        case inr assump_20 =>
          cases assump_20
          case intro assump_44 assump_45 =>
            have assump_191 : p2 := by
              exact assump_45
            let assump_52 := assump_15 assump_191
            apply False.elim assump_52
      case inr assump_16 =>
        cases assump_14
        case inl assump_58 =>
          cases assump_58
          case inl assump_60 =>
            have assump_192 : (False → False) := by
              intro assump_67
              apply False.elim assump_67
            let assump_66 := assump_2 assump_192
            apply False.elim assump_66
          case inr assump_61 =>
            have assump_193 : (False → False) := by
              intro assump_77
              apply False.elim assump_77
            let assump_76 := assump_2 assump_193
            apply False.elim assump_76
        case inr assump_59 =>
          cases assump_59
          case intro assump_83 assump_84 =>
            have assump_194 : (False → False) := by
              intro assump_93
              apply False.elim assump_93
            let assump_92 := assump_2 assump_194
            apply False.elim assump_92
  case inr assump_8 =>
    cases assump_1
    case intro assump_103 assump_104 =>
      cases assump_103
      case inl assump_105 =>
        cases assump_104
        case inl assump_109 =>
          cases assump_109
          case inl assump_111 =>
            have assump_195 : (False → False) := by
              intro assump_118
              apply False.elim assump_118
            let assump_117 := assump_2 assump_195
            apply False.elim assump_117
          case inr assump_112 =>
            have assump_196 : (False → False) := by
              intro assump_128
              apply False.elim assump_128
            let assump_127 := assump_2 assump_196
            apply False.elim assump_127
        case inr assump_110 =>
          cases assump_110
          case intro assump_134 assump_135 =>
            have assump_197 : p2 := by
              exact assump_135
            let assump_142 := assump_105 assump_197
            apply False.elim assump_142
      case inr assump_106 =>
        cases assump_104
        case inl assump_148 =>
          cases assump_148
          case inl assump_150 =>
            have assump_198 : (False → False) := by
              intro assump_157
              apply False.elim assump_157
            let assump_156 := assump_2 assump_198
            apply False.elim assump_156
          case inr assump_151 =>
            have assump_199 : (False → False) := by
              intro assump_167
              apply False.elim assump_167
            let assump_166 := assump_2 assump_199
            apply False.elim assump_166
        case inr assump_149 =>
          cases assump_149
          case intro assump_173 assump_174 =>
            have assump_200 : (False → False) := by
              intro assump_183
              apply False.elim assump_183
            let assump_182 := assump_2 assump_200
            apply False.elim assump_182


variable (p5 p3 p7 p4 p1 p2 p6 : Prop)
theorem file3_124674 : (((((p1 → False) ∧ (p2 ∧ p7)) ∧ ((p2 ∨ p3) → False)) ∨ (((True → False) → False) → False)) → ((((p4 → p7) ∧ (p3 → p4)) → ((p5 ∨ p2) ∧ (True → p6))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_10
        case intro assump_13 assump_14 =>
          have assump_38 : (p2 ∨ p3) := by
            apply Or.inl
            exact assump_13
          let assump_21 := assump_8 assump_38
          apply False.elim assump_21
  case inr assump_6 =>
    have assump_39 : ((True → False) → False) := by
      intro assump_28
      have assump_40 : True := by
        apply True.intro
      let assump_31 := assump_28 assump_40
      apply False.elim assump_31
    let assump_27 := assump_6 assump_39
    apply False.elim assump_27


variable (p2 p6 p1 p7 p3 p0 p4 p5 : Prop)
theorem file3_125641 : ((((((p1 ∨ p4) ∨ (p4 → False)) ∨ ((p2 ∨ p5) ∨ (p0 → False))) ∨ (((p6 ∧ p4) ∨ (False ∨ p5)) ∨ ((p3 ∨ p0) ∨ (p7 → False)))) ∧ ((((p0 ∧ p1) ∨ (False ∧ False)) → ((True → False) → False)) → (((True → False) ∧ (p3 → p2)) ∧ ((p3 → False) ∧ (True → True))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_8
          case inl assump_10 =>
            have assump_395 : (((p0 ∧ p1) ∨ (False ∧ False)) → ((True → False) → False)) := by
              intro assump_17
              intro assump_18
              cases assump_17
              case inl assump_21 =>
                cases assump_21
                case intro assump_23 assump_24 =>
                  have assump_396 : True := by
                    apply True.intro
                  let assump_31 := assump_18 assump_396
                  apply False.elim assump_31
              case inr assump_22 =>
                cases assump_22
                case intro assump_35 assump_36 =>
                  apply False.elim assump_35
            let assump_16 := assump_3 assump_395
            let assump_39 := And.left assump_16
            let assump_40 := And.left assump_39
            have assump_397 : True := by
              apply True.intro
            let assump_41 := assump_40 assump_397
            apply False.elim assump_41
          case inr assump_11 =>
            have assump_398 : (((p0 ∧ p1) ∨ (False ∧ False)) → ((True → False) → False)) := by
              intro assump_50
              intro assump_51
              cases assump_50
              case inl assump_54 =>
                cases assump_54
                case intro assump_56 assump_57 =>
                  have assump_399 : True := by
                    apply True.intro
                  let assump_64 := assump_51 assump_399
                  apply False.elim assump_64
              case inr assump_55 =>
                cases assump_55
                case intro assump_68 assump_69 =>
                  apply False.elim assump_68
            let assump_49 := assump_3 assump_398
            let assump_72 := And.left assump_49
            let assump_73 := And.left assump_72
            have assump_400 : True := by
              apply True.intro
            let assump_74 := assump_73 assump_400
            apply False.elim assump_74
        case inr assump_9 =>
          have assump_401 : (((p0 ∧ p1) ∨ (False ∧ False)) → ((True → False) → False)) := by
            intro assump_83
            intro assump_84
            cases assump_83
            case inl assump_87 =>
              cases assump_87
              case intro assump_89 assump_90 =>
                have assump_402 : True := by
                  apply True.intro
                let assump_97 := assump_84 assump_402
                apply False.elim assump_97
            case inr assump_88 =>
              cases assump_88
              case intro assump_101 assump_102 =>
                apply False.elim assump_101
          let assump_82 := assump_3 assump_401
          let assump_105 := And.left assump_82
          let assump_106 := And.left assump_105
          have assump_403 : True := by
            apply True.intro
          let assump_107 := assump_106 assump_403
          apply False.elim assump_107
      case inr assump_7 =>
        cases assump_7
        case inl assump_111 =>
          cases assump_111
          case inl assump_113 =>
            have assump_404 : (((p0 ∧ p1) ∨ (False ∧ False)) → ((True → False) → False)) := by
              intro assump_120
              intro assump_121
              cases assump_120
              case inl assump_124 =>
                cases assump_124
                case intro assump_126 assump_127 =>
                  have assump_405 : True := by
                    apply True.intro
                  let assump_134 := assump_121 assump_405
                  apply False.elim assump_134
              case inr assump_125 =>
                cases assump_125
                case intro assump_138 assump_139 =>
                  apply False.elim assump_138
            let assump_119 := assump_3 assump_404
            let assump_142 := And.left assump_119
            let assump_143 := And.left assump_142
            have assump_406 : True := by
              apply True.intro
            let assump_144 := assump_143 assump_406
            apply False.elim assump_144
          case inr assump_114 =>
            have assump_407 : (((p0 ∧ p1) ∨ (False ∧ False)) → ((True → False) → False)) := by
              intro assump_153
              intro assump_154
              cases assump_153
              case inl assump_157 =>
                cases assump_157
                case intro assump_159 assump_160 =>
                  have assump_408 : True := by
                    apply True.intro
                  let assump_167 := assump_154 assump_408
                  apply False.elim assump_167
              case inr assump_158 =>
                cases assump_158
                case intro assump_171 assump_172 =>
                  apply False.elim assump_171
            let assump_152 := assump_3 assump_407
            let assump_175 := And.left assump_152
            let assump_176 := And.left assump_175
            have assump_409 : True := by
              apply True.intro
            let assump_177 := assump_176 assump_409
            apply False.elim assump_177
        case inr assump_112 =>
          have assump_410 : (((p0 ∧ p1) ∨ (False ∧ False)) → ((True → False) → False)) := by
            intro assump_186
            intro assump_187
            cases assump_186
            case inl assump_190 =>
              cases assump_190
              case intro assump_192 assump_193 =>
                have assump_411 : True := by
                  apply True.intro
                let assump_200 := assump_187 assump_411
                apply False.elim assump_200
            case inr assump_191 =>
              cases assump_191
              case intro assump_204 assump_205 =>
                apply False.elim assump_204
          let assump_185 := assump_3 assump_410
          let assump_208 := And.left assump_185
          let assump_209 := And.left assump_208
          have assump_412 : True := by
            apply True.intro
          let assump_210 := assump_209 assump_412
          apply False.elim assump_210
    case inr assump_5 =>
      cases assump_5
      case inl assump_214 =>
        cases assump_214
        case inl assump_216 =>
          cases assump_216
          case intro assump_218 assump_219 =>
            have assump_413 : (((p0 ∧ p1) ∨ (False ∧ False)) → ((True → False) → False)) := by
              intro assump_227
              intro assump_228
              cases assump_227
              case inl assump_231 =>
                cases assump_231
                case intro assump_233 assump_234 =>
                  have assump_414 : True := by
                    apply True.intro
                  let assump_241 := assump_228 assump_414
                  apply False.elim assump_241
              case inr assump_232 =>
                cases assump_232
                case intro assump_245 assump_246 =>
                  apply False.elim assump_245
            let assump_226 := assump_3 assump_413
            let assump_249 := And.left assump_226
            let assump_250 := And.left assump_249
            have assump_415 : True := by
              apply True.intro
            let assump_251 := assump_250 assump_415
            apply False.elim assump_251
        case inr assump_217 =>
          cases assump_217
          case inl assump_255 =>
            apply False.elim assump_255
          case inr assump_256 =>
            have assump_416 : (((p0 ∧ p1) ∨ (False ∧ False)) → ((True → False) → False)) := by
              intro assump_264
              intro assump_265
              cases assump_264
              case inl assump_268 =>
                cases assump_268
                case intro assump_270 assump_271 =>
                  have assump_417 : True := by
                    apply True.intro
                  let assump_278 := assump_265 assump_417
                  apply False.elim assump_278
              case inr assump_269 =>
                cases assump_269
                case intro assump_282 assump_283 =>
                  apply False.elim assump_282
            let assump_263 := assump_3 assump_416
            let assump_286 := And.left assump_263
            let assump_287 := And.left assump_286
            have assump_418 : True := by
              apply True.intro
            let assump_288 := assump_287 assump_418
            apply False.elim assump_288
      case inr assump_215 =>
        cases assump_215
        case inl assump_292 =>
          cases assump_292
          case inl assump_294 =>
            have assump_419 : (((p0 ∧ p1) ∨ (False ∧ False)) → ((True → False) → False)) := by
              intro assump_301
              intro assump_302
              cases assump_301
              case inl assump_305 =>
                cases assump_305
                case intro assump_307 assump_308 =>
                  have assump_420 : True := by
                    apply True.intro
                  let assump_315 := assump_302 assump_420
                  apply False.elim assump_315
              case inr assump_306 =>
                cases assump_306
                case intro assump_319 assump_320 =>
                  apply False.elim assump_319
            let assump_300 := assump_3 assump_419
            let assump_323 := And.left assump_300
            let assump_324 := And.left assump_323
            have assump_421 : True := by
              apply True.intro
            let assump_325 := assump_324 assump_421
            apply False.elim assump_325
          case inr assump_295 =>
            have assump_422 : (((p0 ∧ p1) ∨ (False ∧ False)) → ((True → False) → False)) := by
              intro assump_334
              intro assump_335
              cases assump_334
              case inl assump_338 =>
                cases assump_338
                case intro assump_340 assump_341 =>
                  have assump_423 : True := by
                    apply True.intro
                  let assump_348 := assump_335 assump_423
                  apply False.elim assump_348
              case inr assump_339 =>
                cases assump_339
                case intro assump_352 assump_353 =>
                  apply False.elim assump_352
            let assump_333 := assump_3 assump_422
            let assump_356 := And.left assump_333
            let assump_357 := And.left assump_356
            have assump_424 : True := by
              apply True.intro
            let assump_358 := assump_357 assump_424
            apply False.elim assump_358
        case inr assump_293 =>
          have assump_425 : (((p0 ∧ p1) ∨ (False ∧ False)) → ((True → False) → False)) := by
            intro assump_367
            intro assump_368
            cases assump_367
            case inl assump_371 =>
              cases assump_371
              case intro assump_373 assump_374 =>
                have assump_426 : True := by
                  apply True.intro
                let assump_381 := assump_368 assump_426
                apply False.elim assump_381
            case inr assump_372 =>
              cases assump_372
              case intro assump_385 assump_386 =>
                apply False.elim assump_385
          let assump_366 := assump_3 assump_425
          let assump_389 := And.left assump_366
          let assump_390 := And.left assump_389
          have assump_427 : True := by
            apply True.intro
          let assump_391 := assump_390 assump_427
          apply False.elim assump_391


variable (p7 p4 : Prop)
theorem file3_137656 : (((((p4 ∧ False) ∧ (False ∨ p7)) → False) → False) → False) := by
  intro assump_1
  have assump_17 : (((p4 ∧ False) ∧ (False ∨ p7)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_9
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p0 p5 p2 p7 p4 p1 p6 : Prop)
theorem file3_138099 : (((((p6 → False) ∨ (p6 → p4)) ∧ ((True ∨ p4) → (p2 → False))) → False) → ((((p0 → p2) → (False → p5)) ∨ ((p4 → False) ∧ (False → p7))) ∨ (((p6 ∧ p0) → (p1 ∧ p1)) ∧ ((True ∧ p5) → False)))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  intro assump_5
  apply False.elim assump_5


