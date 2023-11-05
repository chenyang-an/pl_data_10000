variable (p0 p6 p5 p7 : Prop)
theorem file31_38 : ((((((p6 → p6) ∨ (False ∧ True)) ∧ ((False → False) ∨ (p5 → p5))) ∨ (((p7 → p0) ∧ (p5 ∨ p0)) → False)) → False) → False) := by
  intro assump_9
  have assump_22 : ((((p6 → p6) ∨ (False ∧ True)) ∧ ((False → False) ∨ (p5 → p5))) ∨ (((p7 → p0) ∧ (p5 ∨ p0)) → False)) := by
    apply Or.inl
    apply And.intro
    apply Or.inl
    intro assump_13
    exact assump_13
    apply Or.inl
    intro assump_16
    apply False.elim assump_16
  let assump_12 := assump_9 assump_22
  apply False.elim assump_12


variable (p4 p6 p3 p7 p2 p1 p0 : Prop)
theorem file31_600 : ((((((p0 ∧ p7) → (p0 ∨ p7)) → ((p0 ∧ p0) ∨ (p4 → False))) ∧ (((p4 ∧ p6) ∧ (False → p4)) ∧ ((p2 ∨ p6) → (True ∧ p1)))) ∧ ((((p7 ∧ False) → (p3 → False)) ∨ ((False ∨ p3) → False)) → False)) → False) := by
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
            have assump_38 : (((p7 ∧ False) → (p3 → False)) ∨ ((False ∨ p3) → False)) := by
              apply Or.inl
              intro assump_25
              intro assump_26
              cases assump_25
              case intro assump_29 assump_30 =>
                apply False.elim assump_30
            let assump_24 := assump_3 assump_38
            apply False.elim assump_24


variable (p5 p6 p4 p7 p3 p0 p2 : Prop)
theorem file31_1570 : (((((p4 ∧ p7) ∧ (p5 ∧ False)) → False) → False) → ((((p5 ∨ p6) → False) → ((p7 ∧ p0) → False)) → (((p0 → False) ∨ (p7 ∨ p2)) → ((p0 → p3) ∧ (p5 → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  apply And.intro
  intro assump_4
  cases assump_3
  case inl assump_7 =>
    have assump_168 : (((p4 ∧ p7) ∧ (p5 ∧ False)) → False) := by
      intro assump_16
      cases assump_16
      case intro assump_17 assump_18 =>
        cases assump_17
        case intro assump_19 assump_20 =>
          cases assump_18
          case intro assump_25 assump_26 =>
            apply False.elim assump_26
    let assump_15 := assump_1 assump_168
    apply False.elim assump_15
  case inr assump_8 =>
    cases assump_8
    case inl assump_34 =>
      have assump_169 : (((p4 ∧ p7) ∧ (p5 ∧ False)) → False) := by
        intro assump_43
        cases assump_43
        case intro assump_44 assump_45 =>
          cases assump_44
          case intro assump_46 assump_47 =>
            cases assump_45
            case intro assump_52 assump_53 =>
              apply False.elim assump_53
      let assump_42 := assump_1 assump_169
      apply False.elim assump_42
    case inr assump_35 =>
      have assump_170 : (((p4 ∧ p7) ∧ (p5 ∧ False)) → False) := by
        intro assump_68
        cases assump_68
        case intro assump_69 assump_70 =>
          cases assump_69
          case intro assump_71 assump_72 =>
            cases assump_70
            case intro assump_77 assump_78 =>
              apply False.elim assump_78
      let assump_67 := assump_1 assump_170
      apply False.elim assump_67
  intro assump_86
  cases assump_3
  case inl assump_89 =>
    have assump_171 : (((p4 ∧ p7) ∧ (p5 ∧ False)) → False) := by
      intro assump_98
      cases assump_98
      case intro assump_99 assump_100 =>
        cases assump_99
        case intro assump_101 assump_102 =>
          cases assump_100
          case intro assump_107 assump_108 =>
            apply False.elim assump_108
    let assump_97 := assump_1 assump_171
    apply False.elim assump_97
  case inr assump_90 =>
    cases assump_90
    case inl assump_116 =>
      have assump_172 : (((p4 ∧ p7) ∧ (p5 ∧ False)) → False) := by
        intro assump_125
        cases assump_125
        case intro assump_126 assump_127 =>
          cases assump_126
          case intro assump_128 assump_129 =>
            cases assump_127
            case intro assump_134 assump_135 =>
              apply False.elim assump_135
      let assump_124 := assump_1 assump_172
      apply False.elim assump_124
    case inr assump_117 =>
      have assump_173 : (((p4 ∧ p7) ∧ (p5 ∧ False)) → False) := by
        intro assump_150
        cases assump_150
        case intro assump_151 assump_152 =>
          cases assump_151
          case intro assump_153 assump_154 =>
            cases assump_152
            case intro assump_159 assump_160 =>
              apply False.elim assump_160
      let assump_149 := assump_1 assump_173
      apply False.elim assump_149


variable (p2 p6 p5 p0 p4 p7 p3 : Prop)
theorem file31_4670 : (((((p7 → True) ∧ (False → p0)) ∧ ((p0 → p3) → False)) → (((p0 ∨ False) → False) → False)) → ((((p6 → False) ∨ (p6 ∧ p0)) ∧ ((p7 ∨ p0) ∨ (p7 → False))) → (((p2 → p2) ∨ (p3 ∧ p2)) → ((False ∧ p5) → (p5 ∧ p4))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  apply And.intro
  cases assump_4
  case intro assump_5 assump_6 =>
    apply False.elim assump_5
  cases assump_4
  case intro assump_9 assump_10 =>
    apply False.elim assump_9


variable (p1 p0 p3 p2 p7 p6 p4 p5 : Prop)
theorem file31_5202 : (((((p2 → False) ∧ (p4 → p0)) ∧ ((p0 ∧ False) ∧ (p3 → p2))) → (((p0 ∨ p3) ∧ (p0 ∧ p7)) ∧ ((p5 ∧ p6) → (p3 ∧ p1)))) ∨ ((((p6 ∧ p5) → False) ∨ ((p2 → False) → False)) ∨ (((False ∧ p1) → False) ∧ ((p2 → False) → (p7 → False))))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          apply False.elim assump_13
  apply And.intro
  cases assump_1
  case intro assump_18 assump_19 =>
    cases assump_18
    case intro assump_20 assump_21 =>
      cases assump_19
      case intro assump_26 assump_27 =>
        cases assump_26
        case intro assump_28 assump_29 =>
          apply False.elim assump_29
  cases assump_1
  case intro assump_34 assump_35 =>
    cases assump_34
    case intro assump_36 assump_37 =>
      cases assump_35
      case intro assump_42 assump_43 =>
        cases assump_42
        case intro assump_44 assump_45 =>
          apply False.elim assump_45
  intro assump_50
  apply And.intro
  cases assump_50
  case intro assump_51 assump_52 =>
    cases assump_1
    case intro assump_57 assump_58 =>
      cases assump_57
      case intro assump_59 assump_60 =>
        cases assump_58
        case intro assump_65 assump_66 =>
          cases assump_65
          case intro assump_67 assump_68 =>
            apply False.elim assump_68
  cases assump_50
  case intro assump_73 assump_74 =>
    cases assump_1
    case intro assump_79 assump_80 =>
      cases assump_79
      case intro assump_81 assump_82 =>
        cases assump_80
        case intro assump_87 assump_88 =>
          cases assump_87
          case intro assump_89 assump_90 =>
            apply False.elim assump_90


variable (p6 p3 p5 p0 : Prop)
theorem file31_7128 : ((((((p5 ∧ p6) ∧ (False ∨ False)) → False) ∧ (((p0 → p6) → (False → False)) ∨ ((p3 → False) → (p5 → False)))) → False) → False) := by
  intro assump_10
  have assump_36 : ((((p5 ∧ p6) ∧ (False ∨ False)) → False) ∧ (((p0 → p6) → (False → False)) ∨ ((p3 → False) → (p5 → False)))) := by
    apply And.intro
    intro assump_14
    cases assump_14
    case intro assump_15 assump_16 =>
      cases assump_15
      case intro assump_17 assump_18 =>
        cases assump_16
        case inl assump_23 =>
          apply False.elim assump_23
        case inr assump_24 =>
          apply False.elim assump_24
    apply Or.inl
    intro assump_29
    intro assump_30
    apply False.elim assump_30
  let assump_13 := assump_10 assump_36
  apply False.elim assump_13


variable (p3 p5 p1 p4 p6 : Prop)
theorem file31_7944 : (((((p5 ∧ p4) ∨ (p1 → p1)) ∧ ((p3 → p3) ∨ (p5 → p6))) → False) → False) := by
  intro assump_35
  have assump_48 : (((p5 ∧ p4) ∨ (p1 → p1)) ∧ ((p3 → p3) ∨ (p5 → p6))) := by
    apply And.intro
    apply Or.inr
    intro assump_39
    exact assump_39
    apply Or.inl
    intro assump_42
    exact assump_42
  let assump_38 := assump_35 assump_48
  apply False.elim assump_38


variable (p1 p7 p4 p2 p5 p3 : Prop)
theorem file31_8379 : ((((((p5 ∧ p4) ∨ (p2 ∨ True)) → False) → (((p2 ∨ p1) ∧ (p5 → False)) → ((p7 → p3) ∧ (p4 → False)))) → False) → False) := by
  intro assump_1
  have assump_64 : ((((p5 ∧ p4) ∨ (p2 ∨ True)) → False) → (((p2 ∨ p1) ∧ (p5 → False)) → ((p7 → p3) ∧ (p4 → False)))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      cases assump_10
      case inl assump_12 =>
        have assump_65 : ((p5 ∧ p4) ∨ (p2 ∨ True)) := by
          apply Or.inr
          apply Or.inl
          exact assump_12
        let assump_20 := assump_5 assump_65
        apply False.elim assump_20
      case inr assump_13 =>
        have assump_66 : ((p5 ∧ p4) ∨ (p2 ∨ True)) := by
          apply Or.inr
          apply Or.inr
          apply True.intro
        let assump_30 := assump_5 assump_66
        apply False.elim assump_30
    intro assump_34
    cases assump_6
    case intro assump_37 assump_38 =>
      cases assump_37
      case inl assump_39 =>
        have assump_67 : ((p5 ∧ p4) ∨ (p2 ∨ True)) := by
          apply Or.inr
          apply Or.inl
          exact assump_39
        let assump_47 := assump_5 assump_67
        apply False.elim assump_47
      case inr assump_40 =>
        have assump_68 : ((p5 ∧ p4) ∨ (p2 ∨ True)) := by
          apply Or.inr
          apply Or.inr
          apply True.intro
        let assump_57 := assump_5 assump_68
        apply False.elim assump_57
  let assump_4 := assump_1 assump_64
  apply False.elim assump_4


variable (p6 p1 p0 p3 p5 p4 p7 : Prop)
theorem file31_9972 : (((((True → p0) ∧ (p0 ∧ p1)) → ((False → False) ∧ (p0 ∨ False))) ∨ (((p6 → p0) → (p5 → p5)) → False)) ∨ ((((False → p6) → (True → False)) ∨ ((False → False) → (p4 ∧ p1))) ∨ (((p6 → p7) → (p0 ∨ p3)) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  apply False.elim assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      apply Or.inl
      exact assump_9


variable (p7 p6 p0 p2 p1 p3 p5 : Prop)
theorem file31_10507 : (((((p2 → p1) ∨ (p3 → False)) ∧ ((p2 → p0) ∧ (p3 ∧ False))) ∧ (((p3 → p0) → (p5 → p7)) → ((p0 ∨ p6) ∨ (p5 → False)))) → False) := by
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
            apply False.elim assump_15
      case inr assump_7 =>
        cases assump_5
        case intro assump_22 assump_23 =>
          cases assump_23
          case intro assump_26 assump_27 =>
            apply False.elim assump_27


variable (p1 p7 p2 p0 : Prop)
theorem file31_11240 : ((((((p1 → False) ∨ (False ∧ p0)) → ((p2 → False) ∨ (False ∧ p7))) → (((True ∧ False) ∧ (p2 ∨ False)) → False)) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p1 → False) ∨ (False ∧ p0)) → ((p2 → False) ∨ (False ∧ p7))) → (((True ∧ False) ∧ (p2 ∨ False)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        apply False.elim assump_10
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p4 : Prop)
theorem file31_11826 : ((((((True ∨ p4) ∧ (False → False)) → False) → False) → False) → False) := by
  intro assump_9
  have assump_26 : ((((True ∨ p4) ∧ (False → False)) → False) → False) := by
    intro assump_13
    have assump_27 : ((True ∨ p4) ∧ (False → False)) := by
      apply And.intro
      apply Or.inl
      apply True.intro
      intro assump_17
      apply False.elim assump_17
    let assump_16 := assump_13 assump_27
    apply False.elim assump_16
  let assump_12 := assump_9 assump_26
  apply False.elim assump_12


variable (p5 p1 p2 : Prop)
theorem file31_12386 : ((((((p2 ∨ True) → False) → ((False ∨ False) → False)) → (((False ∨ p1) ∧ (False ∧ p2)) → ((p5 ∧ True) → False))) → False) → False) := by
  intro assump_1
  have assump_29 : ((((p2 ∨ True) → False) → ((False ∨ False) → False)) → (((False ∨ p1) ∧ (False ∧ p2)) → ((p5 ∧ True) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_7
    case intro assump_8 assump_9 =>
      cases assump_6
      case intro assump_14 assump_15 =>
        cases assump_14
        case inl assump_16 =>
          apply False.elim assump_16
        case inr assump_17 =>
          cases assump_15
          case intro assump_22 assump_23 =>
            apply False.elim assump_22
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p2 p1 p3 p7 p5 : Prop)
theorem file31_13203 : (((((True ∨ True) ∨ (p3 → False)) ∨ ((p7 → True) → False)) ∧ (((p2 → False) → (p5 → True)) → False)) → ((((False → False) → (True ∧ p1)) → False) ∧ (((p5 → False) ∧ (False → False)) ∧ ((False → p7) → (p2 ∨ p7))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_9
        case inl assump_11 =>
          have assump_158 : ((p2 → False) → (p5 → True)) := by
            intro assump_18
            intro assump_19
            apply True.intro
          let assump_17 := assump_6 assump_158
          apply False.elim assump_17
        case inr assump_12 =>
          have assump_159 : ((p2 → False) → (p5 → True)) := by
            intro assump_28
            intro assump_29
            apply True.intro
          let assump_27 := assump_6 assump_159
          apply False.elim assump_27
      case inr assump_10 =>
        have assump_160 : ((p2 → False) → (p5 → True)) := by
          intro assump_38
          intro assump_39
          apply True.intro
        let assump_37 := assump_6 assump_160
        apply False.elim assump_37
    case inr assump_8 =>
      have assump_161 : ((p2 → False) → (p5 → True)) := by
        intro assump_48
        intro assump_49
        apply True.intro
      let assump_47 := assump_6 assump_161
      apply False.elim assump_47
  apply And.intro
  apply And.intro
  intro assump_53
  cases assump_1
  case intro assump_56 assump_57 =>
    cases assump_56
    case inl assump_58 =>
      cases assump_58
      case inl assump_60 =>
        cases assump_60
        case inl assump_62 =>
          have assump_162 : ((p2 → False) → (p5 → True)) := by
            intro assump_69
            intro assump_70
            apply True.intro
          let assump_68 := assump_57 assump_162
          apply False.elim assump_68
        case inr assump_63 =>
          have assump_163 : ((p2 → False) → (p5 → True)) := by
            intro assump_79
            intro assump_80
            apply True.intro
          let assump_78 := assump_57 assump_163
          apply False.elim assump_78
      case inr assump_61 =>
        have assump_164 : ((p2 → False) → (p5 → True)) := by
          intro assump_89
          intro assump_90
          apply True.intro
        let assump_88 := assump_57 assump_164
        apply False.elim assump_88
    case inr assump_59 =>
      have assump_165 : ((p2 → False) → (p5 → True)) := by
        intro assump_99
        intro assump_100
        apply True.intro
      let assump_98 := assump_57 assump_165
      apply False.elim assump_98
  intro assump_104
  apply False.elim assump_104
  intro assump_107
  cases assump_1
  case intro assump_110 assump_111 =>
    cases assump_110
    case inl assump_112 =>
      cases assump_112
      case inl assump_114 =>
        cases assump_114
        case inl assump_116 =>
          have assump_166 : ((p2 → False) → (p5 → True)) := by
            intro assump_123
            intro assump_124
            apply True.intro
          let assump_122 := assump_111 assump_166
          apply False.elim assump_122
        case inr assump_117 =>
          have assump_167 : ((p2 → False) → (p5 → True)) := by
            intro assump_133
            intro assump_134
            apply True.intro
          let assump_132 := assump_111 assump_167
          apply False.elim assump_132
      case inr assump_115 =>
        have assump_168 : ((p2 → False) → (p5 → True)) := by
          intro assump_143
          intro assump_144
          apply True.intro
        let assump_142 := assump_111 assump_168
        apply False.elim assump_142
    case inr assump_113 =>
      have assump_169 : ((p2 → False) → (p5 → True)) := by
        intro assump_153
        intro assump_154
        apply True.intro
      let assump_152 := assump_111 assump_169
      apply False.elim assump_152


variable (p3 p7 p0 p1 : Prop)
theorem file31_17220 : (((((p0 → False) ∧ (p1 ∨ False)) → False) ∧ (((p1 → p0) → (p7 ∧ False)) ∧ ((p0 ∨ p7) ∧ (False ∧ p3)))) → False) := by
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
            apply False.elim assump_16
        case inr assump_13 =>
          cases assump_11
          case intro assump_22 assump_23 =>
            apply False.elim assump_22


variable (p2 p5 p7 p0 p4 p1 : Prop)
theorem file31_17884 : (((((True → False) ∨ (p0 ∨ p5)) ∨ ((p2 → False) ∧ (p4 ∧ p7))) → False) → ((((True → p5) ∧ (p1 → False)) → ((False ∧ p1) → False)) ∧ (((True ∨ p2) ∧ (p0 ∧ p2)) → ((p2 → False) → (False → p4))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    apply False.elim assump_4
  intro assump_8
  intro assump_9
  intro assump_10
  apply False.elim assump_10


variable (p2 p1 p0 p5 : Prop)
theorem file31_18369 : ((((((False ∨ False) ∧ (p0 ∧ p5)) ∧ ((p0 ∧ p1) → False)) → (((True → False) ∨ (p2 ∧ True)) → False)) → False) → False) := by
  intro assump_1
  have assump_40 : ((((False ∨ False) ∧ (p0 ∧ p5)) ∧ ((p0 ∧ p1) → False)) → (((True → False) ∨ (p2 ∧ True)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_5
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          cases assump_13
          case inl assump_15 =>
            apply False.elim assump_15
          case inr assump_16 =>
            apply False.elim assump_16
    case inr assump_8 =>
      cases assump_8
      case intro assump_21 assump_22 =>
        cases assump_5
        case intro assump_27 assump_28 =>
          cases assump_27
          case intro assump_29 assump_30 =>
            cases assump_29
            case inl assump_31 =>
              apply False.elim assump_31
            case inr assump_32 =>
              apply False.elim assump_32
  let assump_4 := assump_1 assump_40
  apply False.elim assump_4


variable (p0 p1 p6 p5 p2 : Prop)
theorem file31_19533 : ((((((p2 ∨ p0) ∧ (False ∨ True)) → False) → (((p0 ∨ p6) ∨ (p0 → p0)) ∧ ((True → True) → (p2 → p5)))) ∧ ((((p2 → True) ∨ (True ∧ False)) ∧ ((p0 → p5) → (p1 → True))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : (((p2 → True) ∨ (True ∧ False)) ∧ ((p0 → p5) → (p1 → True))) := by
      apply And.intro
      apply Or.inl
      intro assump_9
      apply True.intro
      intro assump_10
      intro assump_11
      apply True.intro
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p4 p6 p1 p2 p5 p7 p3 : Prop)
theorem file31_20163 : (((((p4 → False) ∨ (p4 → False)) → ((p3 → False) ∨ (p7 → p1))) ∨ (((False → False) ∧ (p1 ∧ p6)) → ((p4 → False) ∧ (p6 → False)))) → ((((p2 → True) → False) → False) ∨ (((p4 ∨ False) → (p5 → False)) → False))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    have assump_24 : (p2 → True) := by
      intro assump_10
      apply True.intro
    let assump_9 := assump_6 assump_24
    apply False.elim assump_9
  case inr assump_3 =>
    apply Or.inl
    intro assump_16
    have assump_25 : (p2 → True) := by
      intro assump_20
      apply True.intro
    let assump_19 := assump_16 assump_25
    apply False.elim assump_19


variable (p7 p1 p6 p4 p2 p0 : Prop)
theorem file31_20900 : (((((p4 ∨ p1) ∨ (p0 ∧ False)) → ((True → p2) ∧ (False ∧ p0))) ∧ (((p6 ∧ p7) ∧ (p2 → False)) ∧ ((p1 → p4) ∧ (p1 ∧ p2)))) → False) := by
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
            cases assump_19
            case intro assump_22 assump_23 =>
              have assump_36 : p2 := by
                exact assump_23
              let assump_32 := assump_9 assump_36
              apply False.elim assump_32


variable (p1 p5 p0 p7 p4 p6 p3 : Prop)
theorem file31_21651 : (((((p1 ∧ p5) ∧ (False ∧ p0)) ∨ ((p3 ∧ True) → False)) ∧ (((False ∧ p7) ∧ (p3 → False)) ∧ ((p1 ∨ p4) → False))) → ((((p7 ∨ p6) ∧ (p1 → False)) ∨ ((True ∨ p6) → False)) → False)) := by
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
            case intro assump_17 assump_18 =>
              cases assump_17
              case intro assump_19 assump_20 =>
                cases assump_18
                case intro assump_25 assump_26 =>
                  apply False.elim assump_25
          case inr assump_16 =>
            cases assump_14
            case intro assump_31 assump_32 =>
              cases assump_31
              case intro assump_33 assump_34 =>
                cases assump_33
                case intro assump_35 assump_36 =>
                  apply False.elim assump_35
      case inr assump_8 =>
        cases assump_1
        case intro assump_43 assump_44 =>
          cases assump_43
          case inl assump_45 =>
            cases assump_45
            case intro assump_47 assump_48 =>
              cases assump_47
              case intro assump_49 assump_50 =>
                cases assump_48
                case intro assump_55 assump_56 =>
                  apply False.elim assump_55
          case inr assump_46 =>
            cases assump_44
            case intro assump_61 assump_62 =>
              cases assump_61
              case intro assump_63 assump_64 =>
                cases assump_63
                case intro assump_65 assump_66 =>
                  apply False.elim assump_65
  case inr assump_4 =>
    cases assump_1
    case intro assump_71 assump_72 =>
      cases assump_71
      case inl assump_73 =>
        cases assump_73
        case intro assump_75 assump_76 =>
          cases assump_75
          case intro assump_77 assump_78 =>
            cases assump_76
            case intro assump_83 assump_84 =>
              apply False.elim assump_83
      case inr assump_74 =>
        cases assump_72
        case intro assump_89 assump_90 =>
          cases assump_89
          case intro assump_91 assump_92 =>
            cases assump_91
            case intro assump_93 assump_94 =>
              apply False.elim assump_93


variable (p2 p7 p1 p5 p6 : Prop)
theorem file31_24182 : ((((((False → False) → (p5 ∨ p6)) → False) → (((p6 ∧ False) ∧ (True ∧ p7)) → ((p2 → False) ∧ (p2 ∨ p1)))) → False) → False) := by
  intro assump_1
  have assump_29 : ((((False → False) → (p5 ∨ p6)) → False) → (((p6 ∧ False) ∧ (True ∧ p7)) → ((p2 → False) ∧ (p2 ∨ p1)))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        apply False.elim assump_13
    cases assump_6
    case intro assump_18 assump_19 =>
      cases assump_18
      case intro assump_20 assump_21 =>
        apply False.elim assump_21
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p1 p0 p2 : Prop)
theorem file31_24959 : ((((((p0 ∧ p1) ∧ (p2 → False)) ∧ ((True → False) ∧ (False ∧ p0))) → False) → False) → False) := by
  intro assump_1
  have assump_29 : ((((p0 ∧ p1) ∧ (p2 → False)) ∧ ((True → False) ∧ (False ∧ p0))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_7
          case intro assump_18 assump_19 =>
            cases assump_19
            case intro assump_22 assump_23 =>
              apply False.elim assump_22
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p1 p0 p4 p7 p3 p2 p6 p5 : Prop)
theorem file31_25686 : ((((((p5 → False) ∧ (p0 ∧ p3)) ∧ ((p1 ∧ p0) → False)) → (((False → False) ∨ (p2 ∧ p2)) ∨ ((p4 → False) → (p1 ∨ p3)))) ∧ ((((p7 → False) ∧ (p4 → p3)) ∧ ((p3 ∨ p4) ∧ (p6 ∨ p3))) ∧ (((p3 → p0) ∨ (p2 → False)) ∧ ((True → False) ∨ (p7 ∧ p7))))) → False) := by
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
              case inl assump_22 =>
                cases assump_7
                case intro assump_26 assump_27 =>
                  cases assump_26
                  case inl assump_28 =>
                    cases assump_27
                    case inl assump_32 =>
                      have assump_267 : True := by
                        apply True.intro
                      let assump_36 := assump_32 assump_267
                      apply False.elim assump_36
                    case inr assump_33 =>
                      cases assump_33
                      case intro assump_40 assump_41 =>
                        have assump_268 : p7 := by
                          exact assump_41
                        let assump_53 := assump_10 assump_268
                        apply False.elim assump_53
                  case inr assump_29 =>
                    cases assump_27
                    case inl assump_59 =>
                      have assump_269 : True := by
                        apply True.intro
                      let assump_63 := assump_59 assump_269
                      apply False.elim assump_63
                    case inr assump_60 =>
                      cases assump_60
                      case intro assump_67 assump_68 =>
                        have assump_270 : p7 := by
                          exact assump_68
                        let assump_79 := assump_10 assump_270
                        apply False.elim assump_79
              case inr assump_23 =>
                cases assump_7
                case intro assump_85 assump_86 =>
                  cases assump_85
                  case inl assump_87 =>
                    cases assump_86
                    case inl assump_91 =>
                      have assump_271 : True := by
                        apply True.intro
                      let assump_95 := assump_91 assump_271
                      apply False.elim assump_95
                    case inr assump_92 =>
                      cases assump_92
                      case intro assump_99 assump_100 =>
                        have assump_272 : p7 := by
                          exact assump_100
                        let assump_112 := assump_10 assump_272
                        apply False.elim assump_112
                  case inr assump_88 =>
                    cases assump_86
                    case inl assump_118 =>
                      have assump_273 : True := by
                        apply True.intro
                      let assump_122 := assump_118 assump_273
                      apply False.elim assump_122
                    case inr assump_119 =>
                      cases assump_119
                      case intro assump_126 assump_127 =>
                        have assump_274 : p7 := by
                          exact assump_127
                        let assump_138 := assump_10 assump_274
                        apply False.elim assump_138
            case inr assump_19 =>
              cases assump_17
              case inl assump_144 =>
                cases assump_7
                case intro assump_148 assump_149 =>
                  cases assump_148
                  case inl assump_150 =>
                    cases assump_149
                    case inl assump_154 =>
                      have assump_275 : True := by
                        apply True.intro
                      let assump_158 := assump_154 assump_275
                      apply False.elim assump_158
                    case inr assump_155 =>
                      cases assump_155
                      case intro assump_162 assump_163 =>
                        have assump_276 : p7 := by
                          exact assump_163
                        let assump_175 := assump_10 assump_276
                        apply False.elim assump_175
                  case inr assump_151 =>
                    cases assump_149
                    case inl assump_181 =>
                      have assump_277 : True := by
                        apply True.intro
                      let assump_185 := assump_181 assump_277
                      apply False.elim assump_185
                    case inr assump_182 =>
                      cases assump_182
                      case intro assump_189 assump_190 =>
                        have assump_278 : p7 := by
                          exact assump_190
                        let assump_202 := assump_10 assump_278
                        apply False.elim assump_202
              case inr assump_145 =>
                cases assump_7
                case intro assump_208 assump_209 =>
                  cases assump_208
                  case inl assump_210 =>
                    cases assump_209
                    case inl assump_214 =>
                      have assump_279 : True := by
                        apply True.intro
                      let assump_218 := assump_214 assump_279
                      apply False.elim assump_218
                    case inr assump_215 =>
                      cases assump_215
                      case intro assump_222 assump_223 =>
                        have assump_280 : p7 := by
                          exact assump_223
                        let assump_236 := assump_10 assump_280
                        apply False.elim assump_236
                  case inr assump_211 =>
                    cases assump_209
                    case inl assump_242 =>
                      have assump_281 : True := by
                        apply True.intro
                      let assump_246 := assump_242 assump_281
                      apply False.elim assump_246
                    case inr assump_243 =>
                      cases assump_243
                      case intro assump_250 assump_251 =>
                        have assump_282 : p7 := by
                          exact assump_251
                        let assump_263 := assump_10 assump_282
                        apply False.elim assump_263


variable (p5 p4 p3 p7 p0 p1 p6 : Prop)
theorem file31_32443 : (((((p1 → p6) → False) ∨ ((p1 → False) → False)) ∨ (((True → p3) ∨ (p4 → False)) ∧ ((False → p6) ∨ (p7 ∧ p1)))) → ((((True → False) → (True ∨ False)) → ((p7 → p4) ∧ (p3 → p4))) → (((p0 ∨ p0) ∨ (p6 → False)) → ((False ∧ False) → (p5 ∨ p0))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply False.elim assump_5


variable (p6 p3 p2 p7 : Prop)
theorem file31_32894 : (((((p2 ∨ p6) ∨ (p3 → p7)) → False) ∧ (((False → False) ∨ (p3 ∧ p7)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : ((False → False) ∨ (p3 ∧ p7)) := by
      apply Or.inl
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p0 p3 p4 p7 p6 p2 p1 : Prop)
theorem file31_33317 : ((((((p0 ∨ p4) → (p6 ∧ p1)) → ((p2 → p3) → False)) → (((p1 ∨ p0) ∨ (p4 → p1)) ∨ ((p0 ∧ p7) → (p0 → p7)))) ∧ ((((False → False) → False) → ((p1 → False) ∨ (p3 ∨ p3))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_26 : (((False → False) → False) → ((p1 → False) ∨ (p3 ∨ p3))) := by
      intro assump_9
      apply Or.inl
      intro assump_12
      have assump_27 : (False → False) := by
        intro assump_17
        apply False.elim assump_17
      let assump_16 := assump_9 assump_27
      apply False.elim assump_16
    let assump_8 := assump_3 assump_26
    apply False.elim assump_8


variable (p0 p4 p7 p1 p2 p3 p5 p6 : Prop)
theorem file31_34036 : (((((False ∨ p0) → False) → False) → (((p5 ∨ p1) ∧ (p7 ∧ p3)) → ((p7 → False) → False))) → ((((p4 → p5) → (False ∧ p2)) ∨ ((p6 ∧ p2) ∧ (p3 ∧ p4))) → (((p2 → p0) → False) → ((True ∨ p0) ∨ (False ∨ True))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    apply Or.inl
    apply Or.inl
    apply True.intro
  case inr assump_7 =>
    cases assump_7
    case intro assump_12 assump_13 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        cases assump_13
        case intro assump_20 assump_21 =>
          apply Or.inl
          apply Or.inl
          apply True.intro


variable (p4 p3 : Prop)
theorem file31_34723 : ((((((p3 → p3) ∨ (p4 → False)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p3 → p3) ∨ (p4 → False)) → False) → False) := by
    intro assump_5
    have assump_19 : ((p3 → p3) ∨ (p4 → False)) := by
      apply Or.inl
      intro assump_9
      exact assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p0 p4 p7 p1 p6 p3 p2 : Prop)
theorem file31_35216 : ((((((p7 ∧ p3) ∨ (p2 ∧ p6)) ∧ ((p1 ∨ p1) ∨ (p1 ∧ p0))) ∨ (((False → p2) ∨ (p4 → False)) ∨ ((False → False) → False))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p7 ∧ p3) ∨ (p2 ∧ p6)) ∧ ((p1 ∨ p1) ∨ (p1 ∧ p0))) ∨ (((False → p2) ∨ (p4 → False)) ∨ ((False → False) → False))) := by
    apply Or.inr
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p5 p1 p4 p6 p3 p7 p0 : Prop)
theorem file31_35744 : (((((p4 → False) ∨ (p0 ∧ p1)) ∧ ((p5 → False) ∧ (p3 → p7))) → (((True → False) ∧ (p3 → p0)) → ((p7 → p7) → (p6 ∧ p3)))) ∧ ((((p5 → p5) → False) → False) ∨ (((p3 → False) → False) → ((p4 → p7) → False)))) := by
  apply And.intro
  intro assump_5
  intro assump_6
  intro assump_7
  apply And.intro
  cases assump_6
  case intro assump_10 assump_11 =>
    cases assump_5
    case intro assump_16 assump_17 =>
      cases assump_16
      case inl assump_18 =>
        cases assump_17
        case intro assump_22 assump_23 =>
          have assump_116 : True := by
            apply True.intro
          let assump_32 := assump_10 assump_116
          apply False.elim assump_32
      case inr assump_19 =>
        cases assump_19
        case intro assump_36 assump_37 =>
          cases assump_17
          case intro assump_42 assump_43 =>
            have assump_117 : True := by
              apply True.intro
            let assump_53 := assump_10 assump_117
            apply False.elim assump_53
  cases assump_6
  case intro assump_59 assump_60 =>
    cases assump_5
    case intro assump_65 assump_66 =>
      cases assump_65
      case inl assump_67 =>
        cases assump_66
        case intro assump_71 assump_72 =>
          have assump_118 : True := by
            apply True.intro
          let assump_81 := assump_59 assump_118
          apply False.elim assump_81
      case inr assump_68 =>
        cases assump_68
        case intro assump_85 assump_86 =>
          cases assump_66
          case intro assump_91 assump_92 =>
            have assump_119 : True := by
              apply True.intro
            let assump_102 := assump_59 assump_119
            apply False.elim assump_102
  apply Or.inl
  intro assump_106
  have assump_120 : (p5 → p5) := by
    intro assump_110
    exact assump_110
  let assump_109 := assump_106 assump_120
  apply False.elim assump_109


variable (p4 p6 p3 p2 p1 p7 p0 p5 : Prop)
theorem file31_37701 : (((((p0 ∨ False) → (p1 ∨ p7)) ∨ ((p5 → p3) ∧ (p1 → p5))) → False) → ((((p3 ∨ True) → False) → ((p4 ∨ p4) → False)) → (((p6 → p6) ∧ (p2 ∧ False)) → ((False → False) → (True → False))))) := by
  intro assump_12
  intro assump_13
  intro assump_14
  intro assump_15
  intro assump_16
  cases assump_14
  case intro assump_21 assump_22 =>
    cases assump_22
    case intro assump_25 assump_26 =>
      apply False.elim assump_26


variable (p6 p2 p0 p4 p1 p7 : Prop)
theorem file31_38187 : (((((p0 ∨ p1) ∨ (p2 → p2)) → False) → (((p1 → p6) ∨ (True → p6)) ∧ ((p4 ∨ p1) ∨ (p0 → p7)))) ∨ ((((p0 ∧ p1) ∧ (p7 ∨ p1)) ∧ ((p7 → False) ∨ (False → p1))) → False)) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  apply Or.inl
  intro assump_4
  have assump_22 : ((p0 ∨ p1) ∨ (p2 → p2)) := by
    apply Or.inl
    apply Or.inr
    exact assump_4
  let assump_8 := assump_1 assump_22
  apply False.elim assump_8
  apply Or.inr
  intro assump_14
  have assump_23 : ((p0 ∨ p1) ∨ (p2 → p2)) := by
    apply Or.inl
    apply Or.inl
    exact assump_14
  let assump_18 := assump_1 assump_23
  apply False.elim assump_18


variable (p6 p3 p1 p0 p4 p7 : Prop)
theorem file31_38869 : (((((p7 ∧ p1) → False) → ((p0 → p4) → False)) → (((True → p0) → False) ∨ ((p0 → p6) → False))) → ((((p0 → False) → (True ∨ False)) ∨ ((p6 ∧ p6) → (p6 → False))) ∨ (((p6 ∨ True) ∨ (p7 ∨ p6)) → ((p3 ∧ p4) → (p4 ∧ p1))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  apply Or.inl
  apply True.intro


variable (p5 p3 p6 p0 p2 p4 p7 p1 : Prop)
theorem file31_39258 : (((((True → False) → (p6 ∧ p4)) → False) ∨ (((p2 → False) → (p2 ∨ p2)) ∨ ((p1 ∧ p3) ∧ (p0 → False)))) → ((((p5 → False) ∧ (True → False)) → False) ∨ (((p3 ∧ p7) → False) → False))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      have assump_53 : True := by
        apply True.intro
      let assump_13 := assump_8 assump_53
      apply False.elim assump_13
  case inr assump_3 =>
    cases assump_3
    case inl assump_17 =>
      apply Or.inl
      intro assump_21
      cases assump_21
      case intro assump_22 assump_23 =>
        have assump_54 : True := by
          apply True.intro
        let assump_28 := assump_23 assump_54
        apply False.elim assump_28
    case inr assump_18 =>
      cases assump_18
      case intro assump_32 assump_33 =>
        cases assump_32
        case intro assump_34 assump_35 =>
          apply Or.inl
          intro assump_42
          cases assump_42
          case intro assump_43 assump_44 =>
            have assump_55 : True := by
              apply True.intro
            let assump_49 := assump_44 assump_55
            apply False.elim assump_49


variable (p7 p5 p3 p6 p1 p2 p4 : Prop)
theorem file31_40536 : ((((((p4 ∧ p6) ∧ (p7 ∧ True)) ∧ ((p3 → True) ∧ (p6 → False))) ∧ (((p6 → False) ∨ (p1 → p3)) ∧ ((p5 ∧ p6) → False))) ∧ ((((p3 → False) ∨ (p5 ∧ p2)) ∧ ((p4 → False) ∧ (p6 ∧ True))) ∧ (((p7 → p7) ∨ (p4 ∧ p4)) → False))) → False) := by
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
              case intro assump_22 assump_23 =>
                cases assump_5
                case intro assump_28 assump_29 =>
                  cases assump_28
                  case inl assump_30 =>
                    cases assump_3
                    case intro assump_36 assump_37 =>
                      cases assump_36
                      case intro assump_38 assump_39 =>
                        cases assump_38
                        case inl assump_40 =>
                          cases assump_39
                          case intro assump_44 assump_45 =>
                            cases assump_45
                            case intro assump_48 assump_49 =>
                              have assump_144 : ((p7 → p7) ∨ (p4 ∧ p4)) := by
                                apply Or.inl
                                intro assump_57
                                exact assump_57
                              let assump_56 := assump_37 assump_144
                              apply False.elim assump_56
                        case inr assump_41 =>
                          cases assump_41
                          case intro assump_63 assump_64 =>
                            cases assump_39
                            case intro assump_69 assump_70 =>
                              cases assump_70
                              case intro assump_73 assump_74 =>
                                have assump_145 : ((p7 → p7) ∨ (p4 ∧ p4)) := by
                                  apply Or.inl
                                  intro assump_82
                                  exact assump_82
                                let assump_81 := assump_37 assump_145
                                apply False.elim assump_81
                  case inr assump_31 =>
                    cases assump_3
                    case intro assump_92 assump_93 =>
                      cases assump_92
                      case intro assump_94 assump_95 =>
                        cases assump_94
                        case inl assump_96 =>
                          cases assump_95
                          case intro assump_100 assump_101 =>
                            cases assump_101
                            case intro assump_104 assump_105 =>
                              have assump_146 : ((p7 → p7) ∨ (p4 ∧ p4)) := by
                                apply Or.inl
                                intro assump_113
                                exact assump_113
                              let assump_112 := assump_93 assump_146
                              apply False.elim assump_112
                        case inr assump_97 =>
                          cases assump_97
                          case intro assump_119 assump_120 =>
                            cases assump_95
                            case intro assump_125 assump_126 =>
                              cases assump_126
                              case intro assump_129 assump_130 =>
                                have assump_147 : ((p7 → p7) ∨ (p4 ∧ p4)) := by
                                  apply Or.inl
                                  intro assump_138
                                  exact assump_138
                                let assump_137 := assump_93 assump_147
                                apply False.elim assump_137


variable (p4 p2 p3 p1 p7 : Prop)
theorem file31_44586 : (((((p1 → False) → (p2 ∨ True)) ∨ ((p4 → p4) → (p3 → False))) → False) → ((((p4 → False) → False) → ((p2 ∧ p7) → (p1 ∧ p3))) → False)) := by
  intro assump_1
  intro assump_2
  have assump_14 : (((p1 → False) → (p2 ∨ True)) ∨ ((p4 → p4) → (p3 → False))) := by
    apply Or.inl
    intro assump_8
    apply Or.inr
    apply True.intro
  let assump_7 := assump_1 assump_14
  apply False.elim assump_7


variable (p1 p7 p2 p0 p4 : Prop)
theorem file31_45042 : (((((p1 → False) → (p7 → False)) → ((p2 → False) → (True → p0))) ∧ (((False → False) ∨ (False ∨ p4)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : ((False → False) ∨ (False ∨ p4)) := by
      apply Or.inl
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p1 p2 p3 p7 p5 : Prop)
theorem file31_45494 : (((((p7 → False) ∧ (p7 → False)) → ((p1 → False) → (p5 → True))) → False) → ((((p3 → False) → (p5 ∧ True)) → ((p2 → False) → (p3 → False))) → (((p1 ∨ p1) ∧ (p3 → False)) ∧ ((p3 ∧ True) ∧ (p5 → False))))) := by
  intro assump_21
  intro assump_22
  apply And.intro
  apply And.intro
  have assump_73 : (((p7 → False) ∧ (p7 → False)) → ((p1 → False) → (p5 → True))) := by
    intro assump_28
    intro assump_29
    intro assump_30
    apply True.intro
  let assump_27 := assump_21 assump_73
  apply False.elim assump_27
  intro assump_34
  have assump_74 : (((p7 → False) ∧ (p7 → False)) → ((p1 → False) → (p5 → True))) := by
    intro assump_42
    intro assump_43
    intro assump_44
    apply True.intro
  let assump_41 := assump_21 assump_74
  apply False.elim assump_41
  apply And.intro
  apply And.intro
  have assump_75 : (((p7 → False) ∧ (p7 → False)) → ((p1 → False) → (p5 → True))) := by
    intro assump_53
    intro assump_54
    intro assump_55
    apply True.intro
  let assump_52 := assump_21 assump_75
  apply False.elim assump_52
  apply True.intro
  intro assump_59
  have assump_76 : (((p7 → False) ∧ (p7 → False)) → ((p1 → False) → (p5 → True))) := by
    intro assump_67
    intro assump_68
    intro assump_69
    apply True.intro
  let assump_66 := assump_21 assump_76
  apply False.elim assump_66


variable (p4 p3 p0 p7 p6 : Prop)
theorem file31_46872 : (((((True ∧ False) ∨ (p0 → p4)) ∨ ((p4 → p6) ∧ (False → p6))) ∧ (((True ∧ False) ∨ (p3 ∨ True)) ∧ ((p0 ∧ p7) ∧ (True ∧ False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          apply False.elim assump_9
      case inr assump_7 =>
        cases assump_3
        case intro assump_16 assump_17 =>
          cases assump_16
          case inl assump_18 =>
            cases assump_18
            case intro assump_20 assump_21 =>
              apply False.elim assump_21
          case inr assump_19 =>
            cases assump_19
            case inl assump_26 =>
              cases assump_17
              case intro assump_30 assump_31 =>
                cases assump_30
                case intro assump_32 assump_33 =>
                  cases assump_31
                  case intro assump_38 assump_39 =>
                    apply False.elim assump_39
            case inr assump_27 =>
              cases assump_17
              case intro assump_46 assump_47 =>
                cases assump_46
                case intro assump_48 assump_49 =>
                  cases assump_47
                  case intro assump_54 assump_55 =>
                    apply False.elim assump_55
    case inr assump_5 =>
      cases assump_5
      case intro assump_60 assump_61 =>
        cases assump_3
        case intro assump_66 assump_67 =>
          cases assump_66
          case inl assump_68 =>
            cases assump_68
            case intro assump_70 assump_71 =>
              apply False.elim assump_71
          case inr assump_69 =>
            cases assump_69
            case inl assump_76 =>
              cases assump_67
              case intro assump_80 assump_81 =>
                cases assump_80
                case intro assump_82 assump_83 =>
                  cases assump_81
                  case intro assump_88 assump_89 =>
                    apply False.elim assump_89
            case inr assump_77 =>
              cases assump_67
              case intro assump_96 assump_97 =>
                cases assump_96
                case intro assump_98 assump_99 =>
                  cases assump_97
                  case intro assump_104 assump_105 =>
                    apply False.elim assump_105


variable (p7 p6 p4 p1 p2 p0 p5 p3 : Prop)
theorem file31_49361 : (((((p7 → True) ∨ (p6 ∨ p5)) → False) ∧ (((p2 → False) ∧ (p1 → p3)) ∨ ((p3 → False) ∨ (p4 ∧ p1)))) → ((((p2 → p3) → False) → ((p0 ∧ p0) → (p5 ∨ p0))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case inl assump_9 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        have assump_47 : ((p7 → True) ∨ (p6 ∨ p5)) := by
          apply Or.inl
          intro assump_20
          apply True.intro
        let assump_19 := assump_5 assump_47
        apply False.elim assump_19
    case inr assump_10 =>
      cases assump_10
      case inl assump_24 =>
        have assump_48 : ((p7 → True) ∨ (p6 ∨ p5)) := by
          apply Or.inl
          intro assump_30
          apply True.intro
        let assump_29 := assump_5 assump_48
        apply False.elim assump_29
      case inr assump_25 =>
        cases assump_25
        case intro assump_34 assump_35 =>
          have assump_49 : ((p7 → True) ∨ (p6 ∨ p5)) := by
            apply Or.inl
            intro assump_43
            apply True.intro
          let assump_42 := assump_5 assump_49
          apply False.elim assump_42


variable (p1 p2 p4 p6 p3 p7 p5 : Prop)
theorem file31_50598 : (((((p1 → False) → False) → ((p4 ∧ False) ∧ (p1 ∧ False))) → (((p1 → False) ∧ (p2 ∨ p5)) → ((p1 ∧ p3) → False))) ∨ ((((p6 → False) ∨ (p7 ∧ p2)) ∧ ((p3 → p7) ∨ (p2 ∨ p6))) → (((False ∧ p6) ∨ (True → p1)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_2
    case intro assump_10 assump_11 =>
      cases assump_11
      case inl assump_14 =>
        have assump_52 : ((p1 → False) → False) := by
          intro assump_21
          have assump_53 : p1 := by
            exact assump_4
          let assump_24 := assump_21 assump_53
          apply False.elim assump_24
        let assump_20 := assump_1 assump_52
        let assump_28 := And.left assump_20
        let assump_29 := And.right assump_28
        apply False.elim assump_29
      case inr assump_15 =>
        have assump_54 : ((p1 → False) → False) := by
          intro assump_39
          have assump_55 : p1 := by
            exact assump_4
          let assump_42 := assump_39 assump_55
          apply False.elim assump_42
        let assump_38 := assump_1 assump_54
        let assump_46 := And.left assump_38
        let assump_47 := And.right assump_46
        apply False.elim assump_47


variable (p1 p6 p0 p7 p3 : Prop)
theorem file31_51917 : ((((((p7 → True) ∨ (p6 → False)) → ((p0 → p6) → False)) → (((False ∧ p6) ∧ (p1 → p3)) → False)) → False) → False) := by
  intro assump_42
  have assump_57 : ((((p7 → True) ∨ (p6 → False)) → ((p0 → p6) → False)) → (((False ∧ p6) ∧ (p1 → p3)) → False)) := by
    intro assump_46
    intro assump_47
    cases assump_47
    case intro assump_48 assump_49 =>
      cases assump_48
      case intro assump_50 assump_51 =>
        apply False.elim assump_50
  let assump_45 := assump_42 assump_57
  apply False.elim assump_45


variable (p3 p5 p2 p1 p0 p7 : Prop)
theorem file31_52497 : ((((((p2 ∧ p3) ∧ (p1 → p5)) ∨ ((p1 ∧ p3) ∨ (p1 → True))) ∨ (((False ∨ p0) ∧ (False ∨ p0)) → ((p3 ∧ p2) ∨ (p5 → p7)))) ∧ ((((p0 ∧ False) ∧ (p1 → p5)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_8
          case intro assump_10 assump_11 =>
            have assump_90 : (((p0 ∧ False) ∧ (p1 → p5)) → False) := by
              intro assump_21
              cases assump_21
              case intro assump_22 assump_23 =>
                cases assump_22
                case intro assump_24 assump_25 =>
                  apply False.elim assump_25
            let assump_20 := assump_3 assump_90
            apply False.elim assump_20
      case inr assump_7 =>
        cases assump_7
        case inl assump_33 =>
          cases assump_33
          case intro assump_35 assump_36 =>
            have assump_91 : (((p0 ∧ False) ∧ (p1 → p5)) → False) := by
              intro assump_44
              cases assump_44
              case intro assump_45 assump_46 =>
                cases assump_45
                case intro assump_47 assump_48 =>
                  apply False.elim assump_48
            let assump_43 := assump_3 assump_91
            apply False.elim assump_43
        case inr assump_34 =>
          have assump_92 : (((p0 ∧ False) ∧ (p1 → p5)) → False) := by
            intro assump_61
            cases assump_61
            case intro assump_62 assump_63 =>
              cases assump_62
              case intro assump_64 assump_65 =>
                apply False.elim assump_65
          let assump_60 := assump_3 assump_92
          apply False.elim assump_60
    case inr assump_5 =>
      have assump_93 : (((p0 ∧ False) ∧ (p1 → p5)) → False) := by
        intro assump_78
        cases assump_78
        case intro assump_79 assump_80 =>
          cases assump_79
          case intro assump_81 assump_82 =>
            apply False.elim assump_82
      let assump_77 := assump_3 assump_93
      apply False.elim assump_77


variable (p1 p6 p4 p5 p0 p3 p2 p7 : Prop)
theorem file31_54747 : ((((((p2 ∧ p3) → (False → p5)) ∨ ((True ∨ p0) ∧ (False ∨ p4))) ∨ (((p6 → p3) ∨ (p0 ∨ p1)) → ((False ∧ p1) → False))) ∧ ((((False ∨ p0) ∧ (p0 ∧ False)) ∨ ((p7 → False) → (p7 → p7))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        have assump_80 : (((False ∨ p0) ∧ (p0 ∧ False)) ∨ ((p7 → False) → (p7 → p7))) := by
          apply Or.inr
          intro assump_13
          intro assump_14
          exact assump_14
        let assump_12 := assump_3 assump_80
        apply False.elim assump_12
      case inr assump_7 =>
        cases assump_7
        case intro assump_22 assump_23 =>
          cases assump_22
          case inl assump_24 =>
            cases assump_23
            case inl assump_28 =>
              apply False.elim assump_28
            case inr assump_29 =>
              have assump_81 : (((False ∨ p0) ∧ (p0 ∧ False)) ∨ ((p7 → False) → (p7 → p7))) := by
                apply Or.inr
                intro assump_37
                intro assump_38
                exact assump_38
              let assump_36 := assump_3 assump_81
              apply False.elim assump_36
          case inr assump_25 =>
            cases assump_23
            case inl assump_48 =>
              apply False.elim assump_48
            case inr assump_49 =>
              have assump_82 : (((False ∨ p0) ∧ (p0 ∧ False)) ∨ ((p7 → False) → (p7 → p7))) := by
                apply Or.inr
                intro assump_57
                intro assump_58
                exact assump_58
              let assump_56 := assump_3 assump_82
              apply False.elim assump_56
    case inr assump_5 =>
      have assump_83 : (((False ∨ p0) ∧ (p0 ∧ False)) ∨ ((p7 → False) → (p7 → p7))) := by
        apply Or.inr
        intro assump_71
        intro assump_72
        exact assump_72
      let assump_70 := assump_3 assump_83
      apply False.elim assump_70


variable (p0 p4 p5 p2 p3 p6 p7 : Prop)
theorem file31_56815 : (((((False → p2) → False) ∨ ((p3 ∨ p5) ∧ (True ∧ False))) → (((p4 → False) ∨ (p2 ∧ False)) ∨ ((p2 → False) ∧ (True → p4)))) ∨ ((((p5 ∧ p5) → False) ∨ ((p6 ∧ p0) ∨ (p4 → p0))) ∨ (((p4 ∨ p7) → False) ∨ ((p3 ∧ True) → False)))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply Or.inl
    intro assump_6
    have assump_37 : (False → p2) := by
      intro assump_11
      apply False.elim assump_11
    let assump_10 := assump_2 assump_37
    apply False.elim assump_10
  case inr assump_3 =>
    cases assump_3
    case intro assump_17 assump_18 =>
      cases assump_17
      case inl assump_19 =>
        cases assump_18
        case intro assump_23 assump_24 =>
          apply False.elim assump_24
      case inr assump_20 =>
        cases assump_18
        case intro assump_31 assump_32 =>
          apply False.elim assump_32


variable (p3 p0 p5 p4 p2 p7 : Prop)
theorem file31_57761 : (((((p4 ∨ p7) ∧ (True ∧ p3)) → False) → False) → ((((True ∧ p7) ∨ (p5 ∧ p7)) ∧ ((p0 ∧ False) ∧ (p5 → p2))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        cases assump_4
        case intro assump_13 assump_14 =>
          cases assump_13
          case intro assump_15 assump_16 =>
            apply False.elim assump_16
    case inr assump_6 =>
      cases assump_6
      case intro assump_21 assump_22 =>
        cases assump_4
        case intro assump_27 assump_28 =>
          cases assump_27
          case intro assump_29 assump_30 =>
            apply False.elim assump_30


variable (p1 p5 p4 p3 p7 p2 p0 : Prop)
theorem file31_58569 : ((((((p7 ∧ False) → False) → ((p4 → p0) ∨ (p7 → False))) → False) ∧ ((((p2 ∧ p2) → (p1 → p3)) ∧ ((p5 → False) ∧ (p5 ∧ p4))) ∧ (((p1 → True) ∨ (p0 ∨ p1)) ∧ ((p1 → False) ∧ (p7 ∧ p4))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          cases assump_13
          case intro assump_16 assump_17 =>
            cases assump_7
            case intro assump_22 assump_23 =>
              cases assump_22
              case inl assump_24 =>
                cases assump_23
                case intro assump_28 assump_29 =>
                  cases assump_29
                  case intro assump_32 assump_33 =>
                    have assump_90 : p5 := by
                      exact assump_16
                    let assump_44 := assump_12 assump_90
                    apply False.elim assump_44
              case inr assump_25 =>
                cases assump_25
                case inl assump_48 =>
                  cases assump_23
                  case intro assump_52 assump_53 =>
                    cases assump_53
                    case intro assump_56 assump_57 =>
                      have assump_91 : p5 := by
                        exact assump_16
                      let assump_68 := assump_12 assump_91
                      apply False.elim assump_68
                case inr assump_49 =>
                  cases assump_23
                  case intro assump_74 assump_75 =>
                    cases assump_75
                    case intro assump_78 assump_79 =>
                      have assump_92 : p1 := by
                        exact assump_49
                      let assump_86 := assump_74 assump_92
                      apply False.elim assump_86


variable (p3 : Prop)
theorem file31_60514 : ((((((False ∧ p3) → False) → False) → False) → False) → False) := by
  intro assump_10
  have assump_29 : ((((False ∧ p3) → False) → False) → False) := by
    intro assump_14
    have assump_30 : ((False ∧ p3) → False) := by
      intro assump_18
      cases assump_18
      case intro assump_19 assump_20 =>
        apply False.elim assump_19
    let assump_17 := assump_14 assump_30
    apply False.elim assump_17
  let assump_13 := assump_10 assump_29
  apply False.elim assump_13


variable (p3 p7 p0 : Prop)
theorem file31_61049 : (((((p3 ∧ p3) ∨ (p3 → p7)) ∨ ((p0 ∨ p7) → False)) → False) → False) := by
  intro assump_1
  have assump_16 : (((p3 ∧ p3) ∨ (p3 → p7)) ∨ ((p0 ∨ p7) → False)) := by
    apply Or.inl
    apply Or.inr
    intro assump_5
    have assump_17 : (((p3 ∧ p3) ∨ (p3 → p7)) ∨ ((p0 ∨ p7) → False)) := by
      apply Or.inl
      apply Or.inl
      apply And.intro
      exact assump_5
      exact assump_5
    let assump_9 := assump_1 assump_17
    apply False.elim assump_9
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p0 p1 p7 p5 p2 p4 p6 : Prop)
theorem file31_61640 : (((((p4 ∧ p7) → False) ∧ ((p0 → False) → (p0 → p6))) → False) → ((((p0 ∧ p0) ∨ (True ∨ p4)) ∧ ((p1 → p4) ∧ (p6 ∧ True))) → (((p2 ∧ p5) → (False → p0)) ∨ ((p0 ∧ False) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        cases assump_4
        case intro assump_13 assump_14 =>
          cases assump_14
          case intro assump_17 assump_18 =>
            apply Or.inl
            intro assump_25
            intro assump_26
            apply False.elim assump_26
    case inr assump_6 =>
      cases assump_6
      case inl assump_29 =>
        cases assump_4
        case intro assump_33 assump_34 =>
          cases assump_34
          case intro assump_37 assump_38 =>
            apply Or.inl
            intro assump_45
            intro assump_46
            apply False.elim assump_46
      case inr assump_30 =>
        cases assump_4
        case intro assump_51 assump_52 =>
          cases assump_52
          case intro assump_55 assump_56 =>
            apply Or.inl
            intro assump_63
            intro assump_64
            apply False.elim assump_64


variable (p7 p5 : Prop)
theorem file31_62928 : (((((p5 ∧ False) ∧ (p7 ∧ p5)) → False) → False) → False) := by
  intro assump_1
  have assump_17 : (((p5 ∧ False) ∧ (p7 ∧ p5)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_9
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p0 p6 : Prop)
theorem file31_63350 : (((((False ∨ True) → False) → ((p6 → False) → (p0 → p0))) → False) → False) := by
  intro assump_1
  have assump_17 : (((False ∨ True) → False) → ((p6 → False) → (p0 → p0))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    exact assump_7
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p5 p6 p1 p4 p3 : Prop)
theorem file31_63728 : ((((((True ∧ False) → (p1 ∨ p1)) ∨ ((p4 → p3) → (p4 ∧ p3))) ∨ (((p6 ∨ p5) ∧ (p3 → False)) ∧ ((p4 → p5) → False))) → False) → False) := by
  intro assump_5
  have assump_19 : ((((True ∧ False) → (p1 ∨ p1)) ∨ ((p4 → p3) → (p4 ∧ p3))) ∨ (((p6 ∨ p5) ∧ (p3 → False)) ∧ ((p4 → p5) → False))) := by
    apply Or.inl
    apply Or.inl
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      apply False.elim assump_11
  let assump_8 := assump_5 assump_19
  apply False.elim assump_8


variable (p1 p6 p0 p3 p7 p4 p2 : Prop)
theorem file31_64291 : ((((((p6 → p7) → (p7 ∧ p3)) → ((False → False) ∨ (p6 ∧ True))) → False) ∧ ((((p2 ∧ True) → (p1 ∨ True)) → False) ∨ (((True ∧ p3) ∨ (True ∧ p0)) ∨ ((p1 ∧ p0) → (p6 → p4))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      have assump_72 : ((p2 ∧ True) → (p1 ∨ True)) := by
        intro assump_11
        cases assump_11
        case intro assump_12 assump_13 =>
          apply Or.inr
          apply True.intro
      let assump_10 := assump_6 assump_72
      apply False.elim assump_10
    case inr assump_7 =>
      cases assump_7
      case inl assump_21 =>
        cases assump_21
        case inl assump_23 =>
          cases assump_23
          case intro assump_25 assump_26 =>
            have assump_73 : (((p6 → p7) → (p7 ∧ p3)) → ((False → False) ∨ (p6 ∧ True))) := by
              intro assump_33
              apply Or.inl
              intro assump_36
              apply False.elim assump_36
            let assump_32 := assump_2 assump_73
            apply False.elim assump_32
        case inr assump_24 =>
          cases assump_24
          case intro assump_42 assump_43 =>
            have assump_74 : (((p6 → p7) → (p7 ∧ p3)) → ((False → False) ∨ (p6 ∧ True))) := by
              intro assump_50
              apply Or.inl
              intro assump_53
              apply False.elim assump_53
            let assump_49 := assump_2 assump_74
            apply False.elim assump_49
      case inr assump_22 =>
        have assump_75 : (((p6 → p7) → (p7 ∧ p3)) → ((False → False) ∨ (p6 ∧ True))) := by
          intro assump_63
          apply Or.inl
          intro assump_66
          apply False.elim assump_66
        let assump_62 := assump_2 assump_75
        apply False.elim assump_62


variable (p7 p4 p2 p0 : Prop)
theorem file31_66145 : ((((((p2 ∨ p2) → False) → False) → (((True → False) → False) ∨ ((p2 → p0) ∧ (p4 → p7)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p2 ∨ p2) → False) → False) → (((True → False) → False) ∨ ((p2 → p0) ∧ (p4 → p7)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    have assump_19 : True := by
      apply True.intro
    let assump_11 := assump_8 assump_19
    apply False.elim assump_11
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p7 p2 p6 p4 p0 p3 p1 : Prop)
theorem file31_66696 : (((((p2 ∧ p4) ∨ (p0 → False)) ∨ ((p7 ∧ p1) ∧ (True ∧ False))) ∧ (((p1 ∨ p3) → (p0 ∨ True)) ∨ ((p6 → p3) → (p1 → False)))) → ((((True ∨ True) → False) → ((p3 → False) → False)) ∨ (((True ∧ p7) → False) ∧ ((p3 ∨ p6) → False)))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_3
          case inl assump_14 =>
            apply Or.inl
            intro assump_18
            intro assump_19
            have assump_82 : (True ∨ True) := by
              apply Or.inl
              apply True.intro
            let assump_24 := assump_18 assump_82
            apply False.elim assump_24
          case inr assump_15 =>
            apply Or.inl
            intro assump_30
            intro assump_31
            have assump_83 : (True ∨ True) := by
              apply Or.inl
              apply True.intro
            let assump_36 := assump_30 assump_83
            apply False.elim assump_36
      case inr assump_7 =>
        cases assump_3
        case inl assump_42 =>
          apply Or.inl
          intro assump_46
          intro assump_47
          have assump_84 : (True ∨ True) := by
            apply Or.inl
            apply True.intro
          let assump_52 := assump_46 assump_84
          apply False.elim assump_52
        case inr assump_43 =>
          apply Or.inl
          intro assump_58
          intro assump_59
          have assump_85 : (True ∨ True) := by
            apply Or.inl
            apply True.intro
          let assump_64 := assump_58 assump_85
          apply False.elim assump_64
    case inr assump_5 =>
      cases assump_5
      case intro assump_68 assump_69 =>
        cases assump_68
        case intro assump_70 assump_71 =>
          cases assump_69
          case intro assump_76 assump_77 =>
            apply False.elim assump_77


variable (p1 p5 p2 p6 p4 : Prop)
theorem file31_68740 : (((((p6 ∨ p4) ∧ (p2 ∨ p1)) → ((False → p5) ∨ (p5 → True))) → False) → False) := by
  intro assump_1
  have assump_41 : (((p6 ∨ p4) ∧ (p2 ∨ p1)) → ((False → p5) ∨ (p5 → True))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case inl assump_12 =>
          apply Or.inl
          intro assump_16
          apply False.elim assump_16
        case inr assump_13 =>
          apply Or.inl
          intro assump_21
          apply False.elim assump_21
      case inr assump_9 =>
        cases assump_7
        case inl assump_26 =>
          apply Or.inl
          intro assump_30
          apply False.elim assump_30
        case inr assump_27 =>
          apply Or.inl
          intro assump_35
          apply False.elim assump_35
  let assump_4 := assump_1 assump_41
  apply False.elim assump_4


variable (p4 p5 : Prop)
theorem file31_69694 : ((((((p4 → False) → (p4 → False)) → ((True ∨ p5) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_26 : ((((p4 → False) → (p4 → False)) → ((True ∨ p5) → False)) → False) := by
    intro assump_5
    have assump_27 : ((p4 → False) → (p4 → False)) := by
      intro assump_9
      intro assump_10
      have assump_28 : p4 := by
        exact assump_10
      let assump_15 := assump_9 assump_28
      apply False.elim assump_15
    let assump_8 := assump_5 assump_27
    have assump_29 : (True ∨ p5) := by
      apply Or.inl
      apply True.intro
    let assump_19 := assump_8 assump_29
    apply False.elim assump_19
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p7 p4 p3 p2 : Prop)
theorem file31_70454 : (((((True ∧ True) ∧ (p3 → False)) → ((p7 ∧ p4) → (p2 → True))) → False) → False) := by
  intro assump_1
  have assump_11 : (((True ∧ True) ∧ (p3 → False)) → ((p7 ∧ p4) → (p2 → True))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p2 p6 p0 p5 p7 : Prop)
theorem file31_70844 : (((((True → False) → (False ∧ True)) → ((p2 ∧ p7) ∨ (p2 ∨ p2))) → False) → ((((p2 ∨ p2) ∨ (p7 → p2)) → ((False ∨ p7) ∨ (p7 → p7))) ∨ (((p0 → p5) → (p5 ∧ p7)) ∨ ((p6 → False) → (False ∨ p6))))) := by
  intro assump_15
  apply Or.inl
  intro assump_18
  cases assump_18
  case inl assump_19 =>
    cases assump_19
    case inl assump_21 =>
      apply Or.inr
      intro assump_25
      exact assump_25
    case inr assump_22 =>
      apply Or.inr
      intro assump_30
      exact assump_30
  case inr assump_20 =>
    apply Or.inr
    intro assump_35
    exact assump_35


variable (p2 p4 p5 p0 : Prop)
theorem file31_71469 : ((((((p2 ∧ p4) → (p2 ∧ p0)) ∧ ((p2 ∨ p2) ∧ (p5 ∧ False))) → False) → False) → False) := by
  intro assump_1
  have assump_33 : ((((p2 ∧ p4) → (p2 ∧ p0)) ∧ ((p2 ∨ p2) ∧ (p5 ∧ False))) → False) := by
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
          cases assump_11
          case intro assump_24 assump_25 =>
            apply False.elim assump_25
  let assump_4 := assump_1 assump_33
  apply False.elim assump_4


variable (p3 p2 p1 p7 p0 p6 p5 : Prop)
theorem file31_72232 : (((((p5 → p1) → False) → False) ∧ (((p6 ∧ False) → (False → False)) → False)) → ((((False ∧ p7) ∧ (p6 → p0)) ∧ ((p6 → False) ∧ (p3 → False))) ∧ (((True ∨ p6) ∨ (False ∨ False)) ∧ ((p0 ∨ p1) ∨ (p2 → False))))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  apply And.intro
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_105 : ((p6 ∧ False) → (False → False)) := by
      intro assump_9
      intro assump_10
      apply False.elim assump_10
    let assump_8 := assump_3 assump_105
    apply False.elim assump_8
  cases assump_1
  case intro assump_16 assump_17 =>
    have assump_106 : ((p6 ∧ False) → (False → False)) := by
      intro assump_23
      intro assump_24
      apply False.elim assump_24
    let assump_22 := assump_17 assump_106
    apply False.elim assump_22
  intro assump_30
  cases assump_1
  case intro assump_33 assump_34 =>
    have assump_107 : ((p6 ∧ False) → (False → False)) := by
      intro assump_40
      intro assump_41
      apply False.elim assump_41
    let assump_39 := assump_34 assump_107
    apply False.elim assump_39
  apply And.intro
  intro assump_47
  cases assump_1
  case intro assump_50 assump_51 =>
    have assump_108 : ((p6 ∧ False) → (False → False)) := by
      intro assump_57
      intro assump_58
      apply False.elim assump_58
    let assump_56 := assump_51 assump_108
    apply False.elim assump_56
  intro assump_64
  cases assump_1
  case intro assump_67 assump_68 =>
    have assump_109 : ((p6 ∧ False) → (False → False)) := by
      intro assump_74
      intro assump_75
      apply False.elim assump_75
    let assump_73 := assump_68 assump_109
    apply False.elim assump_73
  apply And.intro
  cases assump_1
  case intro assump_81 assump_82 =>
    apply Or.inl
    apply Or.inl
    apply True.intro
  cases assump_1
  case intro assump_87 assump_88 =>
    apply Or.inr
    intro assump_93
    have assump_110 : ((p6 ∧ False) → (False → False)) := by
      intro assump_98
      intro assump_99
      apply False.elim assump_99
    let assump_97 := assump_88 assump_110
    apply False.elim assump_97


variable (p2 p4 p6 p0 p3 p7 p5 : Prop)
theorem file31_74412 : (((((p0 ∨ p2) ∨ (False → False)) → False) → (((p5 ∧ p6) ∧ (p5 ∧ p0)) → False)) ∨ ((((p5 → False) → False) ∨ ((p3 ∨ p0) → False)) ∨ (((p6 → False) ∨ (p4 ∧ p6)) → ((p7 ∨ p7) ∧ (p3 ∧ p4))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_4
      case intro assump_11 assump_12 =>
        have assump_23 : ((p0 ∨ p2) ∨ (False → False)) := by
          apply Or.inl
          apply Or.inl
          exact assump_12
        let assump_19 := assump_1 assump_23
        apply False.elim assump_19


variable (p6 p3 p2 p1 p7 : Prop)
theorem file31_75091 : (((((p1 ∨ p1) → (False → False)) → False) → False) ∨ ((((False ∧ p3) ∧ (p2 ∨ p6)) → False) ∧ (((p2 → False) → (p7 ∧ p2)) ∧ ((False → False) → False)))) := by
  apply Or.inl
  intro assump_1
  have assump_12 : ((p1 ∨ p1) → (False → False)) := by
    intro assump_5
    intro assump_6
    apply False.elim assump_6
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p7 p0 p6 p5 p2 p3 : Prop)
theorem file31_75529 : (((((p5 ∨ True) → (p7 → False)) → ((p3 → False) → (p0 ∨ True))) → False) → ((((p6 ∨ True) → False) → False) ∨ (((p2 → False) ∧ (p6 ∨ p7)) → ((p6 ∨ p2) ∨ (p0 → p0))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_11 : (p6 ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_7 := assump_4 assump_11
  apply False.elim assump_7


variable (p7 p6 p2 p4 p3 : Prop)
theorem file31_75948 : ((((((p2 ∧ p2) ∧ (True ∨ p6)) ∧ ((p7 ∧ p2) → False)) → False) ∧ ((((p3 ∨ p6) → False) → False) ∧ (((True ∧ p3) ∨ (p4 ∧ p7)) ∧ ((True → False) ∧ (p3 → p4))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_11
            case intro assump_20 assump_21 =>
              have assump_49 : True := by
                apply True.intro
              let assump_28 := assump_20 assump_49
              apply False.elim assump_28
        case inr assump_13 =>
          cases assump_13
          case intro assump_32 assump_33 =>
            cases assump_11
            case intro assump_38 assump_39 =>
              have assump_50 : True := by
                apply True.intro
              let assump_45 := assump_38 assump_50
              apply False.elim assump_45


variable (p2 p3 p4 p6 p7 p5 p1 : Prop)
theorem file31_77074 : (((((p7 ∧ p7) ∧ (False → p1)) ∧ ((p5 ∨ True) ∨ (False ∧ True))) → (((False → False) → (True → False)) → False)) ∨ ((((p4 ∧ p7) → (False → p2)) → False) ∨ (((p4 ∧ p4) ∨ (p6 → p3)) → ((p6 ∧ p5) ∧ (False ∨ p1))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_6
        case inl assump_17 =>
          cases assump_17
          case inl assump_19 =>
            have assump_52 : (False → False) := by
              intro assump_28
              apply False.elim assump_28
            let assump_27 := assump_2 assump_52
            have assump_53 : True := by
              apply True.intro
            let assump_31 := assump_27 assump_53
            apply False.elim assump_31
          case inr assump_20 =>
            have assump_54 : (False → False) := by
              intro assump_41
              apply False.elim assump_41
            let assump_40 := assump_2 assump_54
            have assump_55 : True := by
              apply True.intro
            let assump_44 := assump_40 assump_55
            apply False.elim assump_44
        case inr assump_18 =>
          cases assump_18
          case intro assump_48 assump_49 =>
            apply False.elim assump_48


variable (p4 p0 p6 p7 p3 p1 p2 p5 : Prop)
theorem file31_78512 : (((((p0 → False) ∧ (True → False)) ∧ ((p1 ∨ p2) → False)) ∧ (((p5 ∨ p7) ∧ (True ∨ p3)) ∨ ((p7 ∧ p3) ∧ (p6 ∨ p4)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_3
        case inl assump_14 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            cases assump_16
            case inl assump_18 =>
              cases assump_17
              case inl assump_22 =>
                have assump_92 : True := by
                  apply True.intro
                let assump_28 := assump_7 assump_92
                apply False.elim assump_28
              case inr assump_23 =>
                have assump_93 : True := by
                  apply True.intro
                let assump_37 := assump_7 assump_93
                apply False.elim assump_37
            case inr assump_19 =>
              cases assump_17
              case inl assump_43 =>
                have assump_94 : True := by
                  apply True.intro
                let assump_49 := assump_7 assump_94
                apply False.elim assump_49
              case inr assump_44 =>
                have assump_95 : True := by
                  apply True.intro
                let assump_58 := assump_7 assump_95
                apply False.elim assump_58
        case inr assump_15 =>
          cases assump_15
          case intro assump_62 assump_63 =>
            cases assump_62
            case intro assump_64 assump_65 =>
              cases assump_63
              case inl assump_70 =>
                have assump_96 : True := by
                  apply True.intro
                let assump_78 := assump_7 assump_96
                apply False.elim assump_78
              case inr assump_71 =>
                have assump_97 : True := by
                  apply True.intro
                let assump_88 := assump_7 assump_97
                apply False.elim assump_88


variable (p4 p7 p6 p1 p3 : Prop)
theorem file31_80624 : (((((p3 ∧ p6) → (True → p6)) → False) ∧ (((False ∧ False) ∧ (p1 ∨ False)) → ((p7 → p4) ∨ (p4 → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_23 : ((p3 ∧ p6) → (True → p6)) := by
      intro assump_10
      intro assump_11
      cases assump_10
      case intro assump_14 assump_15 =>
        exact assump_15
    let assump_9 := assump_2 assump_23
    apply False.elim assump_9


variable (p5 p0 p7 p6 p1 p4 p3 : Prop)
theorem file31_81127 : (((((True ∨ p6) ∧ (p5 ∨ True)) → False) → False) ∨ ((((p4 ∧ True) ∨ (p7 ∧ p5)) ∨ ((p0 ∧ p3) → (p3 ∨ p6))) ∨ (((p5 → False) ∧ (p6 → False)) ∧ ((p4 ∧ p1) ∧ (p1 → p3))))) := by
  apply Or.inl
  intro assump_1
  have assump_8 : ((True ∨ p6) ∧ (p5 ∨ True)) := by
    apply And.intro
    apply Or.inl
    apply True.intro
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p6 p1 p2 p7 p3 p5 p4 : Prop)
theorem file31_81608 : ((((((p6 ∨ p1) ∧ (p6 ∨ p5)) ∨ ((False ∧ p3) ∨ (True ∧ p4))) → (((p3 → p7) ∨ (p3 ∨ p2)) → ((True → False) → False))) → False) → False) := by
  intro assump_1
  have assump_227 : ((((p6 ∨ p1) ∧ (p6 ∨ p5)) ∨ ((False ∧ p3) ∨ (True ∧ p4))) → (((p3 → p7) ∨ (p3 ∨ p2)) → ((True → False) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case inl assump_10 =>
      cases assump_5
      case inl assump_14 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          cases assump_16
          case inl assump_18 =>
            cases assump_17
            case inl assump_22 =>
              have assump_228 : True := by
                apply True.intro
              let assump_29 := assump_7 assump_228
              apply False.elim assump_29
            case inr assump_23 =>
              have assump_229 : True := by
                apply True.intro
              let assump_38 := assump_7 assump_229
              apply False.elim assump_38
          case inr assump_19 =>
            cases assump_17
            case inl assump_44 =>
              have assump_230 : True := by
                apply True.intro
              let assump_51 := assump_7 assump_230
              apply False.elim assump_51
            case inr assump_45 =>
              have assump_231 : True := by
                apply True.intro
              let assump_60 := assump_7 assump_231
              apply False.elim assump_60
      case inr assump_15 =>
        cases assump_15
        case inl assump_64 =>
          cases assump_64
          case intro assump_66 assump_67 =>
            apply False.elim assump_66
        case inr assump_65 =>
          cases assump_65
          case intro assump_70 assump_71 =>
            have assump_232 : True := by
              apply True.intro
            let assump_78 := assump_7 assump_232
            apply False.elim assump_78
    case inr assump_11 =>
      cases assump_11
      case inl assump_82 =>
        cases assump_5
        case inl assump_86 =>
          cases assump_86
          case intro assump_88 assump_89 =>
            cases assump_88
            case inl assump_90 =>
              cases assump_89
              case inl assump_94 =>
                have assump_233 : True := by
                  apply True.intro
                let assump_101 := assump_7 assump_233
                apply False.elim assump_101
              case inr assump_95 =>
                have assump_234 : True := by
                  apply True.intro
                let assump_110 := assump_7 assump_234
                apply False.elim assump_110
            case inr assump_91 =>
              cases assump_89
              case inl assump_116 =>
                have assump_235 : True := by
                  apply True.intro
                let assump_123 := assump_7 assump_235
                apply False.elim assump_123
              case inr assump_117 =>
                have assump_236 : True := by
                  apply True.intro
                let assump_132 := assump_7 assump_236
                apply False.elim assump_132
        case inr assump_87 =>
          cases assump_87
          case inl assump_136 =>
            cases assump_136
            case intro assump_138 assump_139 =>
              apply False.elim assump_138
          case inr assump_137 =>
            cases assump_137
            case intro assump_142 assump_143 =>
              have assump_237 : True := by
                apply True.intro
              let assump_150 := assump_7 assump_237
              apply False.elim assump_150
      case inr assump_83 =>
        cases assump_5
        case inl assump_156 =>
          cases assump_156
          case intro assump_158 assump_159 =>
            cases assump_158
            case inl assump_160 =>
              cases assump_159
              case inl assump_164 =>
                have assump_238 : True := by
                  apply True.intro
                let assump_171 := assump_7 assump_238
                apply False.elim assump_171
              case inr assump_165 =>
                have assump_239 : True := by
                  apply True.intro
                let assump_180 := assump_7 assump_239
                apply False.elim assump_180
            case inr assump_161 =>
              cases assump_159
              case inl assump_186 =>
                have assump_240 : True := by
                  apply True.intro
                let assump_193 := assump_7 assump_240
                apply False.elim assump_193
              case inr assump_187 =>
                have assump_241 : True := by
                  apply True.intro
                let assump_202 := assump_7 assump_241
                apply False.elim assump_202
        case inr assump_157 =>
          cases assump_157
          case inl assump_206 =>
            cases assump_206
            case intro assump_208 assump_209 =>
              apply False.elim assump_208
          case inr assump_207 =>
            cases assump_207
            case intro assump_212 assump_213 =>
              have assump_242 : True := by
                apply True.intro
              let assump_220 := assump_7 assump_242
              apply False.elim assump_220
  let assump_4 := assump_1 assump_227
  apply False.elim assump_4


variable (p2 p6 p3 p1 p4 p5 p7 p0 : Prop)
theorem file31_87026 : (((((p0 ∧ p1) → False) → ((p1 ∨ p6) → (p4 → p7))) ∧ (((p0 → p7) → False) → ((p3 ∨ p2) → (p6 ∧ True)))) → ((((True ∨ p5) → False) → ((p4 ∨ p7) ∧ (p1 → p1))) → (((p7 → p6) ∧ (False → False)) → ((False ∧ p3) → (p3 ∨ p0))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply False.elim assump_5


variable (p2 p5 p0 p4 p7 p6 p1 : Prop)
theorem file31_87465 : (((((p7 ∧ True) → False) ∧ ((p5 ∧ p6) ∧ (p2 → p5))) → (((p6 → False) ∨ (p7 → p0)) ∨ ((p4 → False) ∧ (p5 ∨ True)))) → ((((p5 → p1) ∧ (True ∨ p4)) → False) → (((p2 ∧ True) ∧ (True ∨ True)) → ((False → False) ∨ (p4 ∨ p7))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_4
    case intro assump_6 assump_7 =>
      cases assump_5
      case inl assump_12 =>
        apply Or.inl
        intro assump_20
        apply False.elim assump_20
      case inr assump_13 =>
        apply Or.inl
        intro assump_29
        apply False.elim assump_29


variable (p4 p7 p3 p1 p0 p6 p2 : Prop)
theorem file31_88150 : ((((((False → p1) ∨ (p6 → False)) ∨ ((p0 ∧ p6) → False)) ∨ (((p0 → False) ∧ (False → p4)) → ((p3 → p7) ∧ (p2 ∧ False)))) → False) → False) := by
  intro assump_11
  have assump_21 : ((((False → p1) ∨ (p6 → False)) ∨ ((p0 ∧ p6) → False)) ∨ (((p0 → False) ∧ (False → p4)) → ((p3 → p7) ∧ (p2 ∧ False)))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    intro assump_15
    apply False.elim assump_15
  let assump_14 := assump_11 assump_21
  apply False.elim assump_14


variable (p5 p7 p1 p2 p4 p0 p3 : Prop)
theorem file31_88690 : (((((p5 → p7) → False) → ((p3 → p5) → False)) → (((True → False) → False) ∨ ((p1 → False) ∨ (p1 → False)))) ∨ ((((p4 → False) → (False ∧ p0)) → ((p2 → p0) ∧ (p5 → p2))) ∧ (((True ∨ p2) ∧ (p3 ∧ True)) → False))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_11 : True := by
    apply True.intro
  let assump_7 := assump_4 assump_11
  apply False.elim assump_7


variable (p2 p4 p6 p1 p0 p3 : Prop)
theorem file31_89147 : (((((p4 → True) ∧ (True → p2)) ∧ ((p6 → False) → (p3 → p4))) ∧ (((p1 → True) ∧ (p0 → p2)) ∧ ((True → False) ∧ (p2 → False)))) → ((((p3 → False) ∨ (False → p2)) → False) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_6
        case intro assump_17 assump_18 =>
          cases assump_17
          case intro assump_19 assump_20 =>
            cases assump_18
            case intro assump_25 assump_26 =>
              have assump_36 : True := by
                apply True.intro
              let assump_32 := assump_25 assump_36
              apply False.elim assump_32


variable (p4 p5 p6 p2 p3 p1 p7 : Prop)
theorem file31_89971 : (((((p7 ∧ p4) → (p3 ∧ True)) ∨ ((p6 ∨ p4) ∨ (True → False))) → (((p2 → False) → False) ∧ ((True → False) ∧ (p6 ∧ p1)))) → ((((p6 → False) → False) ∨ ((False ∨ p7) → False)) → (((False ∧ p4) ∧ (p7 → p5)) → ((True ∧ p6) → False)))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_3
    case intro assump_11 assump_12 =>
      cases assump_11
      case intro assump_13 assump_14 =>
        apply False.elim assump_13


variable (p0 p3 p4 p6 p7 p2 p5 : Prop)
theorem file31_90543 : (((((p7 ∧ True) ∨ (False ∨ p4)) ∧ ((p0 ∨ False) → False)) → (((False ∨ p0) → (p2 ∨ p7)) ∨ ((True ∧ p2) → False))) ∧ ((((True ∧ p5) → (p7 → p7)) → False) → (((p0 → False) → False) → ((p6 ∨ False) ∧ (p2 ∨ p3))))) := by
  apply And.intro
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        apply Or.inl
        intro assump_14
        cases assump_14
        case inl assump_15 =>
          apply False.elim assump_15
        case inr assump_16 =>
          apply Or.inr
          exact assump_6
    case inr assump_5 =>
      cases assump_5
      case inl assump_21 =>
        apply False.elim assump_21
      case inr assump_22 =>
        apply Or.inl
        intro assump_29
        cases assump_29
        case inl assump_30 =>
          apply False.elim assump_30
        case inr assump_31 =>
          have assump_79 : (p0 ∨ False) := by
            apply Or.inl
            exact assump_31
          let assump_37 := assump_3 assump_79
          apply False.elim assump_37
  intro assump_41
  intro assump_42
  apply And.intro
  have assump_80 : ((True ∧ p5) → (p7 → p7)) := by
    intro assump_48
    intro assump_49
    cases assump_48
    case intro assump_52 assump_53 =>
      exact assump_49
  let assump_47 := assump_41 assump_80
  apply False.elim assump_47
  have assump_81 : ((True ∧ p5) → (p7 → p7)) := by
    intro assump_66
    intro assump_67
    cases assump_66
    case intro assump_70 assump_71 =>
      exact assump_67
  let assump_65 := assump_41 assump_81
  apply False.elim assump_65


variable (p1 p5 p7 p3 p0 p4 : Prop)
theorem file31_92240 : ((((((p1 ∧ True) ∨ (p3 ∧ p3)) ∨ ((p0 ∧ p5) ∨ (True ∨ p7))) → (((p3 → p0) ∧ (p0 ∧ False)) → ((p3 → p7) → (p4 → p3)))) → False) → False) := by
  intro assump_1
  have assump_26 : ((((p1 ∧ True) ∨ (p3 ∧ p3)) ∨ ((p0 ∧ p5) ∨ (True ∨ p7))) → (((p3 → p0) ∧ (p0 ∧ False)) → ((p3 → p7) → (p4 → p3)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    cases assump_6
    case intro assump_13 assump_14 =>
      cases assump_14
      case intro assump_17 assump_18 =>
        apply False.elim assump_18
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p1 p4 p0 p6 : Prop)
theorem file31_92887 : (((((p4 → False) ∧ (False ∨ p4)) ∧ ((False → True) ∧ (True ∨ True))) → False) ∨ ((((False ∨ False) ∨ (p1 ∧ p4)) ∨ ((p1 → p6) → False)) ∧ (((True → False) ∨ (p0 → p1)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        apply False.elim assump_8
      case inr assump_9 =>
        cases assump_3
        case intro assump_14 assump_15 =>
          cases assump_15
          case inl assump_18 =>
            have assump_36 : p4 := by
              exact assump_9
            let assump_24 := assump_4 assump_36
            apply False.elim assump_24
          case inr assump_19 =>
            have assump_37 : p4 := by
              exact assump_9
            let assump_32 := assump_4 assump_37
            apply False.elim assump_32


variable (p3 p5 p0 p2 p4 p1 p6 : Prop)
theorem file31_93844 : (((((True → True) ∧ (p0 → False)) ∨ ((p5 → p6) ∧ (False ∧ p2))) ∧ (((p1 ∨ p6) ∧ (p4 ∨ p5)) ∧ ((False ∨ False) ∨ (p0 ∧ p4)))) → ((((p4 ∧ p0) → (p3 → p6)) ∧ ((p6 ∧ False) → False)) → (((p1 → False) ∨ (p4 ∧ p0)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_2
    case intro assump_8 assump_9 =>
      cases assump_1
      case intro assump_14 assump_15 =>
        cases assump_14
        case inl assump_16 =>
          cases assump_16
          case intro assump_18 assump_19 =>
            cases assump_15
            case intro assump_24 assump_25 =>
              cases assump_24
              case intro assump_26 assump_27 =>
                cases assump_26
                case inl assump_28 =>
                  cases assump_27
                  case inl assump_32 =>
                    cases assump_25
                    case inl assump_36 =>
                      cases assump_36
                      case inl assump_38 =>
                        apply False.elim assump_38
                      case inr assump_39 =>
                        apply False.elim assump_39
                    case inr assump_37 =>
                      cases assump_37
                      case intro assump_44 assump_45 =>
                        have assump_282 : p0 := by
                          exact assump_44
                        let assump_54 := assump_19 assump_282
                        apply False.elim assump_54
                  case inr assump_33 =>
                    cases assump_25
                    case inl assump_60 =>
                      cases assump_60
                      case inl assump_62 =>
                        apply False.elim assump_62
                      case inr assump_63 =>
                        apply False.elim assump_63
                    case inr assump_61 =>
                      cases assump_61
                      case intro assump_68 assump_69 =>
                        have assump_283 : p0 := by
                          exact assump_68
                        let assump_78 := assump_19 assump_283
                        apply False.elim assump_78
                case inr assump_29 =>
                  cases assump_27
                  case inl assump_84 =>
                    cases assump_25
                    case inl assump_88 =>
                      cases assump_88
                      case inl assump_90 =>
                        apply False.elim assump_90
                      case inr assump_91 =>
                        apply False.elim assump_91
                    case inr assump_89 =>
                      cases assump_89
                      case intro assump_96 assump_97 =>
                        have assump_284 : p0 := by
                          exact assump_96
                        let assump_106 := assump_19 assump_284
                        apply False.elim assump_106
                  case inr assump_85 =>
                    cases assump_25
                    case inl assump_112 =>
                      cases assump_112
                      case inl assump_114 =>
                        apply False.elim assump_114
                      case inr assump_115 =>
                        apply False.elim assump_115
                    case inr assump_113 =>
                      cases assump_113
                      case intro assump_120 assump_121 =>
                        have assump_285 : p0 := by
                          exact assump_120
                        let assump_130 := assump_19 assump_285
                        apply False.elim assump_130
        case inr assump_17 =>
          cases assump_17
          case intro assump_134 assump_135 =>
            cases assump_135
            case intro assump_138 assump_139 =>
              apply False.elim assump_138
  case inr assump_5 =>
    cases assump_5
    case intro assump_142 assump_143 =>
      cases assump_2
      case intro assump_148 assump_149 =>
        cases assump_1
        case intro assump_154 assump_155 =>
          cases assump_154
          case inl assump_156 =>
            cases assump_156
            case intro assump_158 assump_159 =>
              cases assump_155
              case intro assump_164 assump_165 =>
                cases assump_164
                case intro assump_166 assump_167 =>
                  cases assump_166
                  case inl assump_168 =>
                    cases assump_167
                    case inl assump_172 =>
                      cases assump_165
                      case inl assump_176 =>
                        cases assump_176
                        case inl assump_178 =>
                          apply False.elim assump_178
                        case inr assump_179 =>
                          apply False.elim assump_179
                      case inr assump_177 =>
                        cases assump_177
                        case intro assump_184 assump_185 =>
                          have assump_286 : p0 := by
                            exact assump_184
                          let assump_194 := assump_159 assump_286
                          apply False.elim assump_194
                    case inr assump_173 =>
                      cases assump_165
                      case inl assump_200 =>
                        cases assump_200
                        case inl assump_202 =>
                          apply False.elim assump_202
                        case inr assump_203 =>
                          apply False.elim assump_203
                      case inr assump_201 =>
                        cases assump_201
                        case intro assump_208 assump_209 =>
                          have assump_287 : p0 := by
                            exact assump_208
                          let assump_218 := assump_159 assump_287
                          apply False.elim assump_218
                  case inr assump_169 =>
                    cases assump_167
                    case inl assump_224 =>
                      cases assump_165
                      case inl assump_228 =>
                        cases assump_228
                        case inl assump_230 =>
                          apply False.elim assump_230
                        case inr assump_231 =>
                          apply False.elim assump_231
                      case inr assump_229 =>
                        cases assump_229
                        case intro assump_236 assump_237 =>
                          have assump_288 : p0 := by
                            exact assump_236
                          let assump_246 := assump_159 assump_288
                          apply False.elim assump_246
                    case inr assump_225 =>
                      cases assump_165
                      case inl assump_252 =>
                        cases assump_252
                        case inl assump_254 =>
                          apply False.elim assump_254
                        case inr assump_255 =>
                          apply False.elim assump_255
                      case inr assump_253 =>
                        cases assump_253
                        case intro assump_260 assump_261 =>
                          have assump_289 : p0 := by
                            exact assump_260
                          let assump_270 := assump_159 assump_289
                          apply False.elim assump_270
          case inr assump_157 =>
            cases assump_157
            case intro assump_274 assump_275 =>
              cases assump_275
              case intro assump_278 assump_279 =>
                apply False.elim assump_278


variable (p1 p3 p0 p2 p4 p6 p5 p7 : Prop)
theorem file31_101660 : (((((p7 ∨ p2) ∨ (False ∧ False)) ∨ ((p5 → False) → False)) → (((p0 → p1) ∨ (p4 ∧ False)) → ((p6 → p0) → (False → False)))) ∨ ((((p6 ∨ p1) ∧ (p0 ∨ p7)) → ((False ∨ False) → False)) ∨ (((p4 ∧ p4) → False) → ((p3 ∧ p5) ∧ (p2 ∧ p1))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  apply False.elim assump_4


variable (p3 p7 p5 p2 p1 p0 : Prop)
theorem file31_102069 : ((((((False ∧ p5) ∧ (p1 ∧ p7)) ∧ ((p2 → False) → False)) → (((p7 ∧ p5) ∧ (p3 → False)) ∨ ((p0 ∧ True) → (p0 → False)))) → False) → False) := by
  intro assump_1
  have assump_17 : ((((False ∧ p5) ∧ (p1 ∧ p7)) ∧ ((p2 → False) → False)) → (((p7 ∧ p5) ∧ (p3 → False)) ∨ ((p0 ∧ True) → (p0 → False)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply False.elim assump_10
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p5 p6 p1 p2 : Prop)
theorem file31_102727 : ((((((p1 → True) ∧ (True ∨ p2)) → False) → (((p6 → p5) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p1 → True) ∧ (True ∨ p2)) → False) → (((p6 → p5) → False) → False)) := by
    intro assump_5
    intro assump_6
    have assump_20 : ((p1 → True) ∧ (True ∨ p2)) := by
      apply And.intro
      intro assump_12
      apply True.intro
      apply Or.inl
      apply True.intro
    let assump_11 := assump_5 assump_20
    apply False.elim assump_11
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p3 p4 p5 p1 p7 p2 : Prop)
theorem file31_103337 : ((((((p4 → False) ∨ (False ∧ p2)) ∨ ((True ∧ p2) ∧ (p5 → p3))) → False) ∧ ((((False → p5) → (p1 → False)) ∨ ((p4 ∧ False) ∧ (p3 ∧ p4))) ∧ (((False → False) ∧ (p7 ∨ True)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        have assump_29 : ((False → False) ∧ (p7 ∨ True)) := by
          apply And.intro
          intro assump_15
          apply False.elim assump_15
          apply Or.inr
          apply True.intro
        let assump_14 := assump_7 assump_29
        apply False.elim assump_14
      case inr assump_9 =>
        cases assump_9
        case intro assump_21 assump_22 =>
          cases assump_21
          case intro assump_23 assump_24 =>
            apply False.elim assump_24


variable (p0 p5 p2 p6 p3 : Prop)
theorem file31_104244 : ((((((p0 → p0) → False) ∧ ((p0 ∨ p5) ∧ (p6 → True))) → (((p2 ∧ p3) → False) ∧ ((p6 ∧ False) → False))) → False) → False) := by
  intro assump_1
  have assump_57 : ((((p0 → p0) → False) ∧ ((p0 ∨ p5) ∧ (p6 → True))) → (((p2 ∧ p3) → False) ∧ ((p6 ∧ False) → False))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_5
      case intro assump_13 assump_14 =>
        cases assump_14
        case intro assump_17 assump_18 =>
          cases assump_17
          case inl assump_19 =>
            have assump_58 : (p0 → p0) := by
              intro assump_28
              exact assump_28
            let assump_27 := assump_13 assump_58
            apply False.elim assump_27
          case inr assump_20 =>
            have assump_59 : (p0 → p0) := by
              intro assump_41
              exact assump_41
            let assump_40 := assump_13 assump_59
            apply False.elim assump_40
    intro assump_47
    cases assump_47
    case intro assump_48 assump_49 =>
      apply False.elim assump_49
  let assump_4 := assump_1 assump_57
  apply False.elim assump_4


variable (p6 p5 p4 p0 p7 p3 p1 : Prop)
theorem file31_105469 : (((((p1 → False) → (p4 → p0)) → ((p6 → False) ∧ (False ∨ p1))) ∨ (((p1 → False) ∧ (p4 → False)) → False)) → ((((p5 ∧ p3) ∨ (p0 → p0)) ∨ ((p4 ∨ p7) → (False ∧ p5))) ∨ (((p7 ∨ p0) ∨ (p0 ∨ p6)) ∧ ((p3 ∧ p4) ∧ (True ∧ p7))))) := by
  intro assump_14
  cases assump_14
  case inl assump_15 =>
    apply Or.inl
    apply Or.inl
    apply Or.inr
    intro assump_19
    exact assump_19
  case inr assump_16 =>
    apply Or.inl
    apply Or.inl
    apply Or.inr
    intro assump_24
    exact assump_24


variable (p7 p3 p2 p5 p4 : Prop)
theorem file31_106020 : ((((((p3 ∨ p5) → False) ∨ ((p4 ∧ p3) ∧ (True → False))) → False) ∧ ((((True ∧ False) → False) ∨ ((p3 → False) → (p7 ∨ p2))) → False)) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    have assump_23 : (((True ∧ False) → False) ∨ ((p3 → False) → (p7 ∨ p2))) := by
      apply Or.inl
      intro assump_13
      cases assump_13
      case intro assump_14 assump_15 =>
        apply False.elim assump_15
    let assump_12 := assump_7 assump_23
    apply False.elim assump_12


variable (p3 p4 p2 p1 p7 p0 p5 : Prop)
theorem file31_106592 : ((((((p5 → False) ∧ (p0 → False)) ∧ ((p5 ∨ p3) ∧ (p3 → False))) → (((p2 ∧ True) ∨ (p1 → p1)) ∧ ((p4 → p5) ∨ (False → p7)))) → False) → False) := by
  intro assump_1
  have assump_66 : ((((p5 → False) ∧ (p0 → False)) ∧ ((p5 ∨ p3) ∧ (p3 → False))) → (((p2 ∧ True) ∨ (p1 → p1)) ∧ ((p4 → p5) ∨ (False → p7)))) := by
    intro assump_5
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case intro assump_14 assump_15 =>
          cases assump_14
          case inl assump_16 =>
            apply Or.inr
            intro assump_22
            exact assump_22
          case inr assump_17 =>
            apply Or.inr
            intro assump_29
            exact assump_29
    cases assump_5
    case intro assump_32 assump_33 =>
      cases assump_32
      case intro assump_34 assump_35 =>
        cases assump_33
        case intro assump_40 assump_41 =>
          cases assump_40
          case inl assump_42 =>
            apply Or.inl
            intro assump_48
            exact assump_42
          case inr assump_43 =>
            apply Or.inl
            intro assump_55
            have assump_67 : p3 := by
              exact assump_43
            let assump_59 := assump_41 assump_67
            apply False.elim assump_59
  let assump_4 := assump_1 assump_66
  apply False.elim assump_4


variable (p3 p6 : Prop)
theorem file31_108052 : ((((((p3 ∨ True) → False) ∧ ((p3 ∨ p6) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_20 : ((((p3 ∨ True) → False) ∧ ((p3 ∨ p6) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_21 : (p3 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_13 := assump_6 assump_21
      apply False.elim assump_13
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p4 p3 : Prop)
theorem file31_108581 : ((((((p3 ∨ False) ∨ (True ∨ p4)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p3 ∨ False) ∨ (True ∨ p4)) → False) → False) := by
    intro assump_5
    have assump_16 : ((p3 ∨ False) ∨ (True ∨ p4)) := by
      apply Or.inr
      apply Or.inl
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p4 p5 : Prop)
theorem file31_109065 : ((((((p4 ∧ p4) → (p5 → p5)) → False) → False) → False) → False) := by
  intro assump_14
  have assump_38 : ((((p4 ∧ p4) → (p5 → p5)) → False) → False) := by
    intro assump_18
    have assump_39 : ((p4 ∧ p4) → (p5 → p5)) := by
      intro assump_22
      intro assump_23
      cases assump_22
      case intro assump_26 assump_27 =>
        exact assump_23
    let assump_21 := assump_18 assump_39
    apply False.elim assump_21
  let assump_17 := assump_14 assump_38
  apply False.elim assump_17


variable (p4 p3 p7 p0 p1 p2 : Prop)
theorem file31_109623 : ((((((True ∧ p0) → (p2 ∧ p2)) ∧ ((p1 ∧ p2) ∨ (p3 → False))) → (((p1 → False) → (False → p7)) ∨ ((p0 → False) ∧ (p4 → False)))) → False) → False) := by
  intro assump_1
  have assump_31 : ((((True ∧ p0) → (p2 ∧ p2)) ∧ ((p1 ∧ p2) ∨ (p3 → False))) → (((p1 → False) → (False → p7)) ∨ ((p0 → False) ∧ (p4 → False)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          apply Or.inl
          intro assump_18
          intro assump_19
          apply False.elim assump_19
      case inr assump_11 =>
        apply Or.inl
        intro assump_24
        intro assump_25
        apply False.elim assump_25
  let assump_4 := assump_1 assump_31
  apply False.elim assump_4


variable (p4 p6 p2 p3 : Prop)
theorem file31_110493 : ((((((True → p3) → False) → ((p3 → False) ∨ (p2 → p3))) ∨ (((True → p4) ∧ (p6 → False)) → False)) → False) → False) := by
  intro assump_1
  have assump_22 : ((((True → p3) → False) → ((p3 → False) ∨ (p2 → p3))) ∨ (((True → p4) ∧ (p6 → False)) → False)) := by
    apply Or.inl
    intro assump_5
    apply Or.inl
    intro assump_8
    have assump_23 : (True → p3) := by
      intro assump_13
      exact assump_8
    let assump_12 := assump_5 assump_23
    apply False.elim assump_12
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p7 p0 p3 p6 p2 p1 p4 : Prop)
theorem file31_111106 : (((((False ∧ p1) ∧ (p7 → p6)) ∧ ((True ∨ True) → (p4 → False))) → (((p1 ∨ p4) → (p2 ∨ p0)) → False)) ∨ ((((p4 ∨ p1) ∨ (p3 → False)) ∧ ((p4 ∨ True) → (p2 → p1))) → (((p4 ∧ p7) → False) → ((p3 → False) ∨ (False → False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        apply False.elim assump_9


variable (p0 p5 p1 p3 p2 p4 p7 : Prop)
theorem file31_111646 : (((((p0 ∨ False) ∨ (p0 ∨ True)) ∧ ((p5 → False) ∨ (p0 → False))) → (((True ∨ p5) → False) → False)) ∨ ((((False ∧ p7) → False) → False) ∧ (((p4 ∨ p1) ∧ (p0 ∨ p3)) ∧ ((p3 → False) ∧ (p0 ∨ p2))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_6
        case inl assump_13 =>
          have assump_69 : (True ∨ p5) := by
            apply Or.inl
            apply True.intro
          let assump_19 := assump_2 assump_69
          apply False.elim assump_19
        case inr assump_14 =>
          have assump_70 : p0 := by
            exact assump_9
          let assump_25 := assump_14 assump_70
          apply False.elim assump_25
      case inr assump_10 =>
        apply False.elim assump_10
    case inr assump_8 =>
      cases assump_8
      case inl assump_31 =>
        cases assump_6
        case inl assump_35 =>
          have assump_71 : (True ∨ p5) := by
            apply Or.inl
            apply True.intro
          let assump_41 := assump_2 assump_71
          apply False.elim assump_41
        case inr assump_36 =>
          have assump_72 : p0 := by
            exact assump_31
          let assump_47 := assump_36 assump_72
          apply False.elim assump_47
      case inr assump_32 =>
        cases assump_6
        case inl assump_53 =>
          have assump_73 : (True ∨ p5) := by
            apply Or.inl
            apply True.intro
          let assump_58 := assump_2 assump_73
          apply False.elim assump_58
        case inr assump_54 =>
          have assump_74 : (True ∨ p5) := by
            apply Or.inl
            apply True.intro
          let assump_65 := assump_2 assump_74
          apply False.elim assump_65


variable (p6 p5 p0 p2 p1 p3 p7 p4 : Prop)
theorem file31_113542 : (((((False ∨ p6) → False) → False) → (((p1 ∧ p6) → (p1 ∨ True)) ∧ ((False → p5) ∨ (p7 → False)))) → ((((p0 → False) ∨ (p7 → False)) ∨ ((p3 ∨ True) ∨ (p4 ∨ p0))) → (((p6 ∨ p2) ∨ (p2 ∨ p4)) → ((p5 ∧ p2) → (p2 ∧ p2))))) := by
  intro assump_12
  intro assump_13
  intro assump_14
  intro assump_15
  apply And.intro
  cases assump_15
  case intro assump_16 assump_17 =>
    cases assump_14
    case inl assump_22 =>
      cases assump_22
      case inl assump_24 =>
        cases assump_13
        case inl assump_28 =>
          cases assump_28
          case inl assump_30 =>
            exact assump_17
          case inr assump_31 =>
            exact assump_17
        case inr assump_29 =>
          cases assump_29
          case inl assump_40 =>
            cases assump_40
            case inl assump_42 =>
              exact assump_17
            case inr assump_43 =>
              exact assump_17
          case inr assump_41 =>
            cases assump_41
            case inl assump_52 =>
              exact assump_17
            case inr assump_53 =>
              exact assump_17
      case inr assump_25 =>
        cases assump_13
        case inl assump_64 =>
          cases assump_64
          case inl assump_66 =>
            exact assump_25
          case inr assump_67 =>
            exact assump_25
        case inr assump_65 =>
          cases assump_65
          case inl assump_76 =>
            cases assump_76
            case inl assump_78 =>
              exact assump_25
            case inr assump_79 =>
              exact assump_25
          case inr assump_77 =>
            cases assump_77
            case inl assump_88 =>
              exact assump_25
            case inr assump_89 =>
              exact assump_25
    case inr assump_23 =>
      cases assump_23
      case inl assump_98 =>
        cases assump_13
        case inl assump_102 =>
          cases assump_102
          case inl assump_104 =>
            exact assump_98
          case inr assump_105 =>
            exact assump_98
        case inr assump_103 =>
          cases assump_103
          case inl assump_114 =>
            cases assump_114
            case inl assump_116 =>
              exact assump_98
            case inr assump_117 =>
              exact assump_98
          case inr assump_115 =>
            cases assump_115
            case inl assump_126 =>
              exact assump_98
            case inr assump_127 =>
              exact assump_98
      case inr assump_99 =>
        cases assump_13
        case inl assump_138 =>
          cases assump_138
          case inl assump_140 =>
            exact assump_17
          case inr assump_141 =>
            exact assump_17
        case inr assump_139 =>
          cases assump_139
          case inl assump_150 =>
            cases assump_150
            case inl assump_152 =>
              exact assump_17
            case inr assump_153 =>
              exact assump_17
          case inr assump_151 =>
            cases assump_151
            case inl assump_162 =>
              exact assump_17
            case inr assump_163 =>
              exact assump_17
  cases assump_15
  case intro assump_172 assump_173 =>
    cases assump_14
    case inl assump_178 =>
      cases assump_178
      case inl assump_180 =>
        cases assump_13
        case inl assump_184 =>
          cases assump_184
          case inl assump_186 =>
            exact assump_173
          case inr assump_187 =>
            exact assump_173
        case inr assump_185 =>
          cases assump_185
          case inl assump_196 =>
            cases assump_196
            case inl assump_198 =>
              exact assump_173
            case inr assump_199 =>
              exact assump_173
          case inr assump_197 =>
            cases assump_197
            case inl assump_208 =>
              exact assump_173
            case inr assump_209 =>
              exact assump_173
      case inr assump_181 =>
        cases assump_13
        case inl assump_220 =>
          cases assump_220
          case inl assump_222 =>
            exact assump_181
          case inr assump_223 =>
            exact assump_181
        case inr assump_221 =>
          cases assump_221
          case inl assump_232 =>
            cases assump_232
            case inl assump_234 =>
              exact assump_181
            case inr assump_235 =>
              exact assump_181
          case inr assump_233 =>
            cases assump_233
            case inl assump_244 =>
              exact assump_181
            case inr assump_245 =>
              exact assump_181
    case inr assump_179 =>
      cases assump_179
      case inl assump_254 =>
        cases assump_13
        case inl assump_258 =>
          cases assump_258
          case inl assump_260 =>
            exact assump_254
          case inr assump_261 =>
            exact assump_254
        case inr assump_259 =>
          cases assump_259
          case inl assump_270 =>
            cases assump_270
            case inl assump_272 =>
              exact assump_254
            case inr assump_273 =>
              exact assump_254
          case inr assump_271 =>
            cases assump_271
            case inl assump_282 =>
              exact assump_254
            case inr assump_283 =>
              exact assump_254
      case inr assump_255 =>
        cases assump_13
        case inl assump_294 =>
          cases assump_294
          case inl assump_296 =>
            exact assump_173
          case inr assump_297 =>
            exact assump_173
        case inr assump_295 =>
          cases assump_295
          case inl assump_306 =>
            cases assump_306
            case inl assump_308 =>
              exact assump_173
            case inr assump_309 =>
              exact assump_173
          case inr assump_307 =>
            cases assump_307
            case inl assump_318 =>
              exact assump_173
            case inr assump_319 =>
              exact assump_173


variable (p6 p3 p4 p1 p2 : Prop)
theorem file31_119650 : ((((((False ∧ p3) → False) → False) → (((p1 ∨ True) → False) ∨ ((p2 → p1) ∧ (p4 ∨ p6)))) → False) → False) := by
  intro assump_1
  have assump_37 : ((((False ∧ p3) → False) → False) → (((p1 ∨ True) → False) ∨ ((p2 → p1) ∧ (p4 ∨ p6)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    cases assump_8
    case inl assump_9 =>
      have assump_38 : ((False ∧ p3) → False) := by
        intro assump_15
        cases assump_15
        case intro assump_16 assump_17 =>
          apply False.elim assump_16
      let assump_14 := assump_5 assump_38
      apply False.elim assump_14
    case inr assump_10 =>
      have assump_39 : ((False ∧ p3) → False) := by
        intro assump_26
        cases assump_26
        case intro assump_27 assump_28 =>
          apply False.elim assump_27
      let assump_25 := assump_5 assump_39
      apply False.elim assump_25
  let assump_4 := assump_1 assump_37
  apply False.elim assump_4


variable (p1 p0 p4 p7 p5 p6 p2 : Prop)
theorem file31_120653 : (((((False ∨ True) ∨ (True → p0)) ∨ ((p2 ∧ p1) → False)) → False) → ((((p1 → False) → (p7 → p5)) ∧ ((p6 ∨ True) ∨ (True ∨ p7))) → (((p0 ∧ p6) ∨ (p6 ∨ p1)) ∨ ((p7 ∨ True) ∨ (p4 ∧ True))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case inl assump_7 =>
      cases assump_7
      case inl assump_9 =>
        apply Or.inl
        apply Or.inr
        apply Or.inl
        exact assump_9
      case inr assump_10 =>
        apply Or.inr
        apply Or.inl
        apply Or.inr
        apply True.intro
    case inr assump_8 =>
      cases assump_8
      case inl assump_19 =>
        apply Or.inr
        apply Or.inl
        apply Or.inr
        apply True.intro
      case inr assump_20 =>
        apply Or.inr
        apply Or.inl
        apply Or.inl
        exact assump_20


