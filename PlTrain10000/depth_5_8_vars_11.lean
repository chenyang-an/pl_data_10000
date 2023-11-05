variable (p1 p2 p3 p0 p4 : Prop)
theorem file11_41 : (((((p1 ∨ p2) ∨ (False → p2)) ∨ ((False → False) → False)) ∨ (((p0 → False) ∧ (p0 ∨ p0)) ∨ ((p3 → False) → False))) ∨ ((((p0 ∨ p4) → False) → False) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inr
  intro assump_1
  apply False.elim assump_1


variable (p7 p6 p3 p1 p4 p2 p5 p0 : Prop)
theorem file11_377 : (((((p6 → True) → (p1 ∧ p3)) ∨ ((True ∧ p7) ∧ (True ∧ p4))) ∧ (((False ∨ False) ∧ (False → p2)) ∧ ((p0 ∧ p0) ∨ (p0 → p0)))) → ((((p7 → p4) ∧ (False → False)) → ((p6 ∨ True) → (p5 → p1))) → False)) := by
  intro assump_10
  intro assump_11
  cases assump_10
  case intro assump_14 assump_15 =>
    cases assump_14
    case inl assump_16 =>
      cases assump_15
      case intro assump_20 assump_21 =>
        cases assump_20
        case intro assump_22 assump_23 =>
          cases assump_22
          case inl assump_24 =>
            apply False.elim assump_24
          case inr assump_25 =>
            apply False.elim assump_25
    case inr assump_17 =>
      cases assump_17
      case intro assump_30 assump_31 =>
        cases assump_30
        case intro assump_32 assump_33 =>
          cases assump_31
          case intro assump_38 assump_39 =>
            cases assump_15
            case intro assump_44 assump_45 =>
              cases assump_44
              case intro assump_46 assump_47 =>
                cases assump_46
                case inl assump_48 =>
                  apply False.elim assump_48
                case inr assump_49 =>
                  apply False.elim assump_49


variable (p2 p6 p5 p7 p3 p0 p4 : Prop)
theorem file11_1649 : (((((p5 → p6) ∨ (p0 ∧ p2)) ∨ ((False ∧ p7) → False)) ∧ (((p3 ∨ p7) ∨ (p5 ∨ p4)) → False)) → ((((True → p7) ∧ (p5 ∨ True)) → ((False ∨ True) ∨ (False → False))) → (((p3 ∧ False) ∧ (p0 → False)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_4
    case intro assump_6 assump_7 =>
      apply False.elim assump_7


variable (p4 p6 p0 p7 : Prop)
theorem file11_2102 : ((((((p6 ∧ False) → False) → ((True → False) ∧ (p4 → False))) → (((p0 → False) → False) → ((p6 → p7) → False))) → False) → False) := by
  intro assump_5
  have assump_34 : ((((p6 ∧ False) → False) → ((True → False) ∧ (p4 → False))) → (((p0 → False) → False) → ((p6 → p7) → False))) := by
    intro assump_9
    intro assump_10
    intro assump_11
    have assump_35 : ((p6 ∧ False) → False) := by
      intro assump_19
      cases assump_19
      case intro assump_20 assump_21 =>
        apply False.elim assump_21
    let assump_18 := assump_9 assump_35
    let assump_26 := And.left assump_18
    have assump_36 : True := by
      apply True.intro
    let assump_27 := assump_26 assump_36
    apply False.elim assump_27
  let assump_8 := assump_5 assump_34
  apply False.elim assump_8


variable (p1 p7 p4 p3 p2 p5 p6 : Prop)
theorem file11_2953 : (((((p3 ∧ p6) ∨ (p6 ∧ p4)) → ((p4 ∨ p6) ∨ (p2 ∧ p4))) ∨ (((p1 ∧ p6) → False) → False)) ∨ ((((p7 ∨ p5) → False) → ((p7 → p3) → (True ∨ p1))) → (((p5 ∧ p6) → (False → False)) → ((p5 → False) ∧ (p6 ∧ p2))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply Or.inl
      apply Or.inr
      exact assump_5
  case inr assump_3 =>
    cases assump_3
    case intro assump_10 assump_11 =>
      apply Or.inl
      apply Or.inl
      exact assump_11


variable (p6 p0 p3 p7 : Prop)
theorem file11_3559 : (((((p0 → False) ∧ (p0 → False)) ∨ ((p7 → False) ∧ (p6 → True))) ∧ (((p7 ∧ p7) ∨ (False → p3)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        have assump_36 : ((p7 ∧ p7) ∨ (False → p3)) := by
          apply Or.inr
          intro assump_15
          apply False.elim assump_15
        let assump_14 := assump_3 assump_36
        apply False.elim assump_14
    case inr assump_5 =>
      cases assump_5
      case intro assump_21 assump_22 =>
        have assump_37 : ((p7 ∧ p7) ∨ (False → p3)) := by
          apply Or.inr
          intro assump_30
          apply False.elim assump_30
        let assump_29 := assump_3 assump_37
        apply False.elim assump_29


variable (p7 p1 p6 p3 p5 : Prop)
theorem file11_4439 : (((((p5 ∧ p1) ∨ (True ∨ p7)) → False) ∧ (((p6 → False) ∨ (p3 → False)) ∧ ((p3 → False) ∧ (True → p7)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case intro assump_12 assump_13 =>
          have assump_42 : ((p5 ∧ p1) ∨ (True ∨ p7)) := by
            apply Or.inr
            apply Or.inl
            apply True.intro
          let assump_22 := assump_2 assump_42
          apply False.elim assump_22
      case inr assump_9 =>
        cases assump_7
        case intro assump_28 assump_29 =>
          have assump_43 : ((p5 ∧ p1) ∨ (True ∨ p7)) := by
            apply Or.inr
            apply Or.inl
            apply True.intro
          let assump_38 := assump_2 assump_43
          apply False.elim assump_38


variable (p6 p0 p4 : Prop)
theorem file11_5379 : (((((p0 ∨ p6) → False) → False) ∧ (((False → p0) → False) ∧ ((p0 → p4) ∧ (p4 → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        have assump_25 : (False → p0) := by
          intro assump_19
          apply False.elim assump_19
        let assump_18 := assump_6 assump_25
        apply False.elim assump_18


variable (p1 p0 p7 p3 p6 p4 p2 p5 : Prop)
theorem file11_5919 : (((((p0 ∧ p7) ∨ (p3 ∨ p6)) ∨ ((p7 → p2) → (p5 → p6))) → (((p1 → False) ∨ (p1 ∨ True)) → ((p4 ∨ p4) ∨ (p5 ∧ p4)))) → ((((p5 ∨ p0) ∧ (p7 ∧ p5)) ∧ ((False → False) → False)) → (((p0 ∧ p4) → (p7 ∨ p7)) ∨ ((p5 ∧ p0) ∨ (p1 ∧ p2))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case inl assump_7 =>
        cases assump_6
        case intro assump_11 assump_12 =>
          apply Or.inl
          intro assump_21
          cases assump_21
          case intro assump_22 assump_23 =>
            apply Or.inl
            exact assump_11
      case inr assump_8 =>
        cases assump_6
        case intro assump_30 assump_31 =>
          apply Or.inl
          intro assump_40
          cases assump_40
          case intro assump_41 assump_42 =>
            apply Or.inl
            exact assump_30


variable (p0 p1 p2 p3 p6 p7 : Prop)
theorem file11_6901 : ((((((p3 ∨ p2) ∨ (False ∧ p6)) ∨ ((p2 ∨ p3) → (True → False))) ∨ (((p0 → False) → (p1 ∨ p0)) → ((p1 → False) → (p7 ∧ False)))) → False) → False) := by
  intro assump_1
  have assump_28 : ((((p3 ∨ p2) ∨ (False ∧ p6)) ∨ ((p2 ∨ p3) → (True → False))) ∨ (((p0 → False) → (p1 ∨ p0)) → ((p1 → False) → (p7 ∧ False)))) := by
    apply Or.inl
    apply Or.inr
    intro assump_5
    intro assump_6
    cases assump_5
    case inl assump_9 =>
      have assump_29 : ((((p3 ∨ p2) ∨ (False ∧ p6)) ∨ ((p2 ∨ p3) → (True → False))) ∨ (((p0 → False) → (p1 ∨ p0)) → ((p1 → False) → (p7 ∧ False)))) := by
        apply Or.inl
        apply Or.inl
        apply Or.inl
        apply Or.inr
        exact assump_9
      let assump_14 := assump_1 assump_29
      apply False.elim assump_14
    case inr assump_10 =>
      have assump_30 : ((((p3 ∨ p2) ∨ (False ∧ p6)) ∨ ((p2 ∨ p3) → (True → False))) ∨ (((p0 → False) → (p1 ∨ p0)) → ((p1 → False) → (p7 ∧ False)))) := by
        apply Or.inl
        apply Or.inl
        apply Or.inl
        apply Or.inl
        exact assump_10
      let assump_21 := assump_1 assump_30
      apply False.elim assump_21
  let assump_4 := assump_1 assump_28
  apply False.elim assump_4


variable (p5 p4 p2 p1 p7 p3 : Prop)
theorem file11_8159 : (((((True → False) → (p1 ∧ p3)) → ((True ∨ False) → (False → False))) ∨ (((p4 → p4) ∨ (p7 ∧ p7)) → ((p2 ∨ p2) → (p1 → False)))) ∨ ((((p2 → True) → False) → False) ∧ (((p4 ∧ p3) ∧ (p5 → False)) ∧ ((False → p5) ∨ (False → p4))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  apply False.elim assump_3


variable (p1 p7 p2 p6 p5 p4 p0 p3 : Prop)
theorem file11_8568 : (((((False ∧ p1) → (p3 ∧ False)) ∧ ((p7 → False) → False)) ∧ (((p5 → True) → False) ∧ ((p2 ∧ p5) ∨ (p1 → True)))) → ((((p5 ∧ p1) ∧ (p0 ∧ p2)) ∨ ((p4 ∧ p5) → False)) ∧ (((False → p4) → (p6 ∨ p7)) ∨ ((p4 ∨ True) → (p5 ∨ p3))))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        cases assump_11
        case inl assump_14 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            apply Or.inr
            intro assump_22
            cases assump_22
            case intro assump_23 assump_24 =>
              have assump_98 : (p5 → True) := by
                intro assump_34
                apply True.intro
              let assump_33 := assump_10 assump_98
              apply False.elim assump_33
        case inr assump_15 =>
          apply Or.inr
          intro assump_40
          cases assump_40
          case intro assump_41 assump_42 =>
            have assump_99 : (p5 → True) := by
              intro assump_51
              apply True.intro
            let assump_50 := assump_10 assump_99
            apply False.elim assump_50
  cases assump_1
  case intro assump_55 assump_56 =>
    cases assump_55
    case intro assump_57 assump_58 =>
      cases assump_56
      case intro assump_63 assump_64 =>
        cases assump_64
        case inl assump_67 =>
          cases assump_67
          case intro assump_69 assump_70 =>
            apply Or.inl
            intro assump_75
            have assump_100 : (p5 → True) := by
              intro assump_82
              apply True.intro
            let assump_81 := assump_63 assump_100
            apply False.elim assump_81
        case inr assump_68 =>
          apply Or.inl
          intro assump_88
          have assump_101 : (p5 → True) := by
            intro assump_94
            apply True.intro
          let assump_93 := assump_63 assump_101
          apply False.elim assump_93


variable (p1 p4 p0 p6 p7 p5 : Prop)
theorem file11_10679 : ((((((True ∨ p7) ∨ (p4 → p5)) ∨ ((True → False) ∨ (p1 → False))) ∨ (((p7 → p0) ∨ (p6 ∨ p0)) → False)) → False) → False) := by
  intro assump_1
  have assump_8 : ((((True ∨ p7) ∨ (p4 → p5)) ∨ ((True → False) ∨ (p1 → False))) ∨ (((p7 → p0) ∨ (p6 ∨ p0)) → False)) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p7 p3 p0 p4 p1 p5 p6 : Prop)
theorem file11_11162 : ((((((p6 ∧ p3) ∧ (True → False)) → ((p7 ∧ p3) ∨ (p3 → p6))) ∨ (((p3 → p7) ∧ (p7 ∨ p0)) → ((p1 ∧ p1) ∧ (p5 ∨ p7)))) ∧ ((((p4 ∨ p1) ∧ (True → True)) → ((False ∨ p3) ∨ (p3 → p0))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_144 : (((p4 ∨ p1) ∧ (True → True)) → ((False ∨ p3) ∨ (p3 → p0))) := by
        intro assump_11
        cases assump_11
        case intro assump_12 assump_13 =>
          cases assump_12
          case inl assump_14 =>
            apply Or.inr
            intro assump_20
            have assump_145 : (((p4 ∨ p1) ∧ (True → True)) → ((False ∨ p3) ∨ (p3 → p0))) := by
              intro assump_28
              cases assump_28
              case intro assump_29 assump_30 =>
                cases assump_29
                case inl assump_31 =>
                  apply Or.inl
                  apply Or.inr
                  exact assump_20
                case inr assump_32 =>
                  apply Or.inl
                  apply Or.inr
                  exact assump_20
            let assump_27 := assump_3 assump_145
            apply False.elim assump_27
          case inr assump_15 =>
            apply Or.inr
            intro assump_48
            have assump_146 : (((p4 ∨ p1) ∧ (True → True)) → ((False ∨ p3) ∨ (p3 → p0))) := by
              intro assump_56
              cases assump_56
              case intro assump_57 assump_58 =>
                cases assump_57
                case inl assump_59 =>
                  apply Or.inl
                  apply Or.inr
                  exact assump_48
                case inr assump_60 =>
                  apply Or.inl
                  apply Or.inr
                  exact assump_48
            let assump_55 := assump_3 assump_146
            apply False.elim assump_55
      let assump_10 := assump_3 assump_144
      apply False.elim assump_10
    case inr assump_5 =>
      have assump_147 : (((p4 ∨ p1) ∧ (True → True)) → ((False ∨ p3) ∨ (p3 → p0))) := by
        intro assump_80
        cases assump_80
        case intro assump_81 assump_82 =>
          cases assump_81
          case inl assump_83 =>
            apply Or.inr
            intro assump_89
            have assump_148 : (((p4 ∨ p1) ∧ (True → True)) → ((False ∨ p3) ∨ (p3 → p0))) := by
              intro assump_97
              cases assump_97
              case intro assump_98 assump_99 =>
                cases assump_98
                case inl assump_100 =>
                  apply Or.inl
                  apply Or.inr
                  exact assump_89
                case inr assump_101 =>
                  apply Or.inl
                  apply Or.inr
                  exact assump_89
            let assump_96 := assump_3 assump_148
            apply False.elim assump_96
          case inr assump_84 =>
            apply Or.inr
            intro assump_117
            have assump_149 : (((p4 ∨ p1) ∧ (True → True)) → ((False ∨ p3) ∨ (p3 → p0))) := by
              intro assump_125
              cases assump_125
              case intro assump_126 assump_127 =>
                cases assump_126
                case inl assump_128 =>
                  apply Or.inl
                  apply Or.inr
                  exact assump_117
                case inr assump_129 =>
                  apply Or.inl
                  apply Or.inr
                  exact assump_117
            let assump_124 := assump_3 assump_149
            apply False.elim assump_124
      let assump_79 := assump_3 assump_147
      apply False.elim assump_79


variable (p5 p3 : Prop)
theorem file11_14829 : ((((((p5 ∧ False) ∧ (p3 ∧ p5)) → ((True ∨ p3) → (False → True))) → (((True → True) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_20 : ((((p5 ∧ False) ∧ (p3 ∧ p5)) → ((True ∨ p3) → (False → True))) → (((True → True) → False) → False)) := by
    intro assump_5
    intro assump_6
    have assump_21 : (True → True) := by
      intro assump_13
      apply True.intro
    let assump_12 := assump_6 assump_21
    apply False.elim assump_12
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p2 p7 : Prop)
theorem file11_15405 : (((((True ∧ p2) → False) → False) ∧ (((p2 → False) → False) → ((p7 ∨ p2) → False))) → ((((True ∨ p2) → False) ∧ ((False → False) ∧ (p2 ∧ True))) → False)) := by
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
          have assump_35 : ((p2 → False) → False) := by
            intro assump_24
            have assump_36 : p2 := by
              exact assump_11
            let assump_27 := assump_24 assump_36
            apply False.elim assump_27
          let assump_23 := assump_18 assump_35
          have assump_37 : (p7 ∨ p2) := by
            apply Or.inr
            exact assump_11
          let assump_31 := assump_23 assump_37
          apply False.elim assump_31


variable (p2 p1 p6 p0 p3 p5 p4 : Prop)
theorem file11_16362 : (((((p3 ∧ p1) → False) ∨ ((False → True) ∧ (True → p0))) ∧ (((p1 → p0) → (p3 ∨ p3)) ∧ ((False → False) → (p5 ∨ p2)))) → ((((False → False) ∨ (p6 ∧ True)) ∨ ((p6 → p0) → False)) ∧ (((p3 ∧ p5) → (False → False)) ∨ ((p1 → p4) ∨ (True ∨ p4))))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        apply Or.inl
        apply Or.inl
        intro assump_14
        apply False.elim assump_14
    case inr assump_5 =>
      cases assump_5
      case intro assump_17 assump_18 =>
        cases assump_3
        case intro assump_23 assump_24 =>
          apply Or.inl
          apply Or.inl
          intro assump_29
          apply False.elim assump_29
  cases assump_1
  case intro assump_32 assump_33 =>
    cases assump_32
    case inl assump_34 =>
      cases assump_33
      case intro assump_38 assump_39 =>
        apply Or.inl
        intro assump_44
        intro assump_45
        apply False.elim assump_45
    case inr assump_35 =>
      cases assump_35
      case intro assump_48 assump_49 =>
        cases assump_33
        case intro assump_54 assump_55 =>
          apply Or.inl
          intro assump_60
          intro assump_61
          apply False.elim assump_61


variable (p5 p2 p7 p1 p6 : Prop)
theorem file11_17747 : (((((p2 ∨ p7) ∧ (p7 ∧ p6)) ∨ ((p5 → p1) → (True ∨ p1))) → False) → False) := by
  intro assump_1
  have assump_11 : (((p2 ∨ p7) ∧ (p7 ∧ p6)) ∨ ((p5 → p1) → (True ∨ p1))) := by
    apply Or.inr
    intro assump_5
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p0 p7 p4 : Prop)
theorem file11_18113 : ((((((p4 ∨ p7) → False) ∧ ((p7 ∧ True) ∧ (p7 → p0))) → False) → False) → False) := by
  intro assump_1
  have assump_30 : ((((p4 ∨ p7) → False) ∧ ((p7 ∧ True) ∧ (p7 → p0))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          have assump_31 : (p4 ∨ p7) := by
            apply Or.inr
            exact assump_12
          let assump_23 := assump_6 assump_31
          apply False.elim assump_23
  let assump_4 := assump_1 assump_30
  apply False.elim assump_4


variable (p2 p1 p5 p7 p3 p6 : Prop)
theorem file11_18806 : (((((p1 → p7) → False) → ((p7 ∧ p5) → False)) → False) → ((((p2 ∨ p3) ∧ (True ∨ p6)) → False) → (((True ∧ p5) ∨ (False ∧ p6)) ∨ ((True ∨ p1) → False)))) := by
  intro assump_14
  intro assump_15
  apply Or.inr
  intro assump_20
  cases assump_20
  case inl assump_21 =>
    have assump_70 : (((p1 → p7) → False) → ((p7 ∧ p5) → False)) := by
      intro assump_26
      intro assump_27
      cases assump_27
      case intro assump_28 assump_29 =>
        have assump_71 : (p1 → p7) := by
          intro assump_37
          exact assump_28
        let assump_36 := assump_26 assump_71
        apply False.elim assump_36
    let assump_25 := assump_14 assump_70
    apply False.elim assump_25
  case inr assump_22 =>
    have assump_72 : (((p1 → p7) → False) → ((p7 ∧ p5) → False)) := by
      intro assump_50
      intro assump_51
      cases assump_51
      case intro assump_52 assump_53 =>
        have assump_73 : (p1 → p7) := by
          intro assump_61
          exact assump_52
        let assump_60 := assump_50 assump_73
        apply False.elim assump_60
    let assump_49 := assump_14 assump_72
    apply False.elim assump_49


variable (p3 p2 p6 p1 p4 p5 : Prop)
theorem file11_20004 : (((((p5 ∧ p1) ∧ (p5 → True)) → ((p3 ∧ p5) → (p1 → False))) ∨ (((p4 ∨ True) ∧ (p4 → False)) → ((p3 → p3) ∨ (p5 → False)))) → ((((p2 → p4) ∧ (p5 → False)) → ((True → False) → False)) ∨ (((p4 → p2) → (p2 ∧ p1)) ∧ ((p4 → p3) ∧ (p6 ∨ p6))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      have assump_40 : True := by
        apply True.intro
      let assump_18 := assump_7 assump_40
      apply False.elim assump_18
  case inr assump_3 =>
    apply Or.inl
    intro assump_24
    intro assump_25
    cases assump_24
    case intro assump_28 assump_29 =>
      have assump_41 : True := by
        apply True.intro
      let assump_36 := assump_25 assump_41
      apply False.elim assump_36


variable (p3 p0 p2 p6 : Prop)
theorem file11_20877 : ((((((p3 ∧ p6) ∧ (p2 → p0)) ∨ ((p6 → False) → False)) → (((False ∨ p2) ∧ (True → False)) → ((False ∨ True) ∨ (True → False)))) → False) → False) := by
  intro assump_1
  have assump_34 : ((((p3 ∧ p6) ∧ (p2 → p0)) ∨ ((p6 → False) → False)) → (((False ∨ p2) ∧ (True → False)) → ((False ∨ True) ∨ (True → False)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        apply False.elim assump_9
      case inr assump_10 =>
        cases assump_5
        case inl assump_17 =>
          cases assump_17
          case intro assump_19 assump_20 =>
            cases assump_19
            case intro assump_21 assump_22 =>
              apply Or.inl
              apply Or.inr
              apply True.intro
        case inr assump_18 =>
          apply Or.inl
          apply Or.inr
          apply True.intro
  let assump_4 := assump_1 assump_34
  apply False.elim assump_4


variable (p2 p6 p0 p3 p7 : Prop)
theorem file11_21905 : (((((p7 ∧ False) → (False ∧ True)) → ((p0 → False) → (p2 → False))) ∧ (((p7 → p3) ∨ (p3 ∧ p0)) → ((p2 ∨ p3) → (p7 ∨ p6)))) → ((((p0 → p0) → False) → False) ∨ (((p0 ∨ p2) → False) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    intro assump_8
    have assump_18 : (p0 → p0) := by
      intro assump_12
      exact assump_12
    let assump_11 := assump_8 assump_18
    apply False.elim assump_11


variable (p1 p2 p0 p5 p3 : Prop)
theorem file11_22414 : (((((True ∨ p0) → (p3 ∨ False)) → False) ∧ (((p1 → p2) → False) ∧ ((False ∧ p5) ∧ (False ∧ p2)))) → False) := by
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


variable (p5 p0 p3 p7 p2 p1 : Prop)
theorem file11_22874 : (((((p5 ∧ p0) ∨ (True ∨ p3)) ∨ ((p2 → p3) ∧ (p5 → False))) → (((False ∧ p7) → (p1 ∧ False)) → False)) → False) := by
  intro assump_7
  have assump_24 : (((p5 ∧ p0) ∨ (True ∨ p3)) ∨ ((p2 → p3) ∧ (p5 → False))) := by
    apply Or.inl
    apply Or.inr
    apply Or.inl
    apply True.intro
  let assump_10 := assump_7 assump_24
  have assump_25 : ((False ∧ p7) → (p1 ∧ False)) := by
    intro assump_12
    apply And.intro
    cases assump_12
    case intro assump_13 assump_14 =>
      apply False.elim assump_13
    cases assump_12
    case intro assump_17 assump_18 =>
      apply False.elim assump_17
  let assump_11 := assump_10 assump_25
  apply False.elim assump_11


variable (p7 p1 p6 : Prop)
theorem file11_23596 : (((((p1 ∨ p7) → (p6 ∨ True)) ∨ ((p1 → False) ∨ (True → False))) → False) → False) := by
  intro assump_10
  have assump_24 : (((p1 ∨ p7) → (p6 ∨ True)) ∨ ((p1 → False) ∨ (True → False))) := by
    apply Or.inl
    intro assump_14
    cases assump_14
    case inl assump_15 =>
      apply Or.inr
      apply True.intro
    case inr assump_16 =>
      apply Or.inr
      apply True.intro
  let assump_13 := assump_10 assump_24
  apply False.elim assump_13


variable (p1 p5 p0 p4 : Prop)
theorem file11_24104 : (((((p1 ∨ p4) ∧ (p4 → p0)) → ((True ∧ p5) → (False → False))) → False) → False) := by
  intro assump_1
  have assump_13 : (((p1 ∨ p4) ∧ (p4 → p0)) → ((True ∧ p5) → (False → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    apply False.elim assump_7
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p5 p2 p1 p3 p4 p0 p6 : Prop)
theorem file11_24507 : (((((p6 ∨ p5) ∧ (True ∨ p3)) ∨ ((p2 ∧ p3) ∨ (p0 → True))) → False) → ((((p6 ∨ p1) ∨ (True ∨ p6)) → ((p0 ∧ p0) → (p4 → True))) ∧ (((p4 ∧ p0) ∨ (p5 → False)) ∨ ((p0 → p6) ∨ (False ∨ p5))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  intro assump_4
  apply True.intro
  apply Or.inl
  apply Or.inr
  intro assump_7
  have assump_15 : (((p6 ∨ p5) ∧ (True ∨ p3)) ∨ ((p2 ∧ p3) ∨ (p0 → True))) := by
    apply Or.inl
    apply And.intro
    apply Or.inr
    exact assump_7
    apply Or.inl
    apply True.intro
  let assump_11 := assump_1 assump_15
  apply False.elim assump_11


variable (p5 p2 p6 p7 p0 p4 p1 : Prop)
theorem file11_25175 : (((((False → False) ∨ (True → False)) ∨ ((p5 ∧ p1) ∧ (p4 → False))) ∨ (((p6 → False) → False) ∧ ((False → False) ∨ (p2 ∨ p4)))) ∨ ((((p7 ∨ p4) ∨ (p6 ∨ p5)) ∧ ((p4 → p0) ∨ (p1 ∨ p4))) ∧ (((p4 ∧ p4) → False) ∨ ((p1 ∧ p2) → False)))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply False.elim assump_1


variable (p2 p5 p3 p6 p0 : Prop)
theorem file11_25574 : (((((p3 ∨ p6) ∨ (p6 → p2)) → False) ∨ (((p5 ∧ False) → False) → ((p0 → True) → False))) → ((((p3 → False) → (p0 → False)) → ((p6 ∧ p0) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    have assump_36 : ((p3 ∨ p6) ∨ (p6 → p2)) := by
      apply Or.inr
      intro assump_10
      have assump_37 : ((p3 ∨ p6) ∨ (p6 → p2)) := by
        apply Or.inl
        apply Or.inr
        exact assump_10
      let assump_14 := assump_5 assump_37
      apply False.elim assump_14
    let assump_9 := assump_5 assump_36
    apply False.elim assump_9
  case inr assump_6 =>
    have assump_38 : ((p5 ∧ False) → False) := by
      intro assump_24
      cases assump_24
      case intro assump_25 assump_26 =>
        apply False.elim assump_26
    let assump_23 := assump_6 assump_38
    have assump_39 : (p0 → True) := by
      intro assump_32
      apply True.intro
    let assump_31 := assump_23 assump_39
    apply False.elim assump_31


variable (p6 p5 p7 p2 p1 p0 p4 : Prop)
theorem file11_26615 : ((((((p5 ∧ p7) ∧ (p5 ∧ p4)) ∨ ((p4 → False) → (p7 → True))) ∧ (((True ∧ p5) ∧ (p2 → False)) → ((True → p2) → False))) ∧ ((((False ∧ p5) ∧ (p5 ∧ p6)) ∧ ((True ∨ p1) ∨ (p7 ∧ p4))) ∧ (((p0 ∧ p6) ∧ (p1 ∨ p4)) → False))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_8
      case inl assump_10 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_13
            case intro assump_20 assump_21 =>
              cases assump_7
              case intro assump_28 assump_29 =>
                cases assump_28
                case intro assump_30 assump_31 =>
                  cases assump_30
                  case intro assump_32 assump_33 =>
                    cases assump_32
                    case intro assump_34 assump_35 =>
                      apply False.elim assump_34
      case inr assump_11 =>
        cases assump_7
        case intro assump_42 assump_43 =>
          cases assump_42
          case intro assump_44 assump_45 =>
            cases assump_44
            case intro assump_46 assump_47 =>
              cases assump_46
              case intro assump_48 assump_49 =>
                apply False.elim assump_48


variable (p6 p1 p2 p3 p0 p7 : Prop)
theorem file11_28030 : (((((p7 ∧ p3) ∨ (p7 ∨ p6)) ∨ ((p2 ∨ p7) ∧ (p1 → False))) → False) → ((((p7 → p7) → (p0 → False)) ∨ ((p6 → False) → False)) → (((False → False) → False) → ((True → p7) → False)))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_2
  case inl assump_9 =>
    have assump_45 : (False → False) := by
      intro assump_22
      apply False.elim assump_22
    let assump_21 := assump_3 assump_45
    apply False.elim assump_21
  case inr assump_10 =>
    have assump_46 : (p6 → False) := by
      intro assump_34
      have assump_47 : (((p7 ∧ p3) ∨ (p7 ∨ p6)) ∨ ((p2 ∨ p7) ∧ (p1 → False))) := by
        apply Or.inl
        apply Or.inr
        apply Or.inr
        exact assump_34
      let assump_38 := assump_1 assump_47
      apply False.elim assump_38
    let assump_33 := assump_10 assump_46
    apply False.elim assump_33


variable (p4 p2 p0 p7 p6 p5 p3 : Prop)
theorem file11_28959 : (((((False → False) ∧ (p0 → False)) → ((p4 ∨ False) ∨ (p4 → p3))) → False) → ((((p4 ∧ p4) → False) → ((p0 ∧ p7) ∧ (p5 → False))) ∧ (((True ∧ False) → (p6 → False)) ∨ ((p5 → False) ∧ (p2 → False))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  apply And.intro
  apply And.intro
  have assump_114 : (((False → False) ∧ (p0 → False)) → ((p4 ∨ False) ∨ (p4 → p3))) := by
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      apply Or.inr
      intro assump_15
      have assump_115 : (((False → False) ∧ (p0 → False)) → ((p4 ∨ False) ∨ (p4 → p3))) := by
        intro assump_22
        cases assump_22
        case intro assump_23 assump_24 =>
          apply Or.inl
          apply Or.inl
          exact assump_15
      let assump_21 := assump_1 assump_115
      apply False.elim assump_21
  let assump_7 := assump_1 assump_114
  apply False.elim assump_7
  have assump_116 : (((False → False) ∧ (p0 → False)) → ((p4 ∨ False) ∨ (p4 → p3))) := by
    intro assump_40
    cases assump_40
    case intro assump_41 assump_42 =>
      apply Or.inr
      intro assump_47
      have assump_117 : (((False → False) ∧ (p0 → False)) → ((p4 ∨ False) ∨ (p4 → p3))) := by
        intro assump_54
        cases assump_54
        case intro assump_55 assump_56 =>
          apply Or.inl
          apply Or.inl
          exact assump_47
      let assump_53 := assump_1 assump_117
      apply False.elim assump_53
  let assump_39 := assump_1 assump_116
  apply False.elim assump_39
  intro assump_67
  have assump_118 : (((False → False) ∧ (p0 → False)) → ((p4 ∨ False) ∨ (p4 → p3))) := by
    intro assump_75
    cases assump_75
    case intro assump_76 assump_77 =>
      apply Or.inr
      intro assump_82
      have assump_119 : (((False → False) ∧ (p0 → False)) → ((p4 ∨ False) ∨ (p4 → p3))) := by
        intro assump_89
        cases assump_89
        case intro assump_90 assump_91 =>
          apply Or.inl
          apply Or.inl
          exact assump_82
      let assump_88 := assump_1 assump_119
      apply False.elim assump_88
  let assump_74 := assump_1 assump_118
  apply False.elim assump_74
  apply Or.inl
  intro assump_104
  intro assump_105
  cases assump_104
  case intro assump_108 assump_109 =>
    apply False.elim assump_109


variable (p5 p2 p3 : Prop)
theorem file11_31285 : ((((((False → False) → (p5 ∧ False)) ∧ ((True ∧ p2) ∨ (p3 → False))) → False) → False) → False) := by
  intro assump_1
  have assump_43 : ((((False → False) → (p5 ∧ False)) ∧ ((True ∧ p2) ∨ (p3 → False))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          have assump_44 : (False → False) := by
            intro assump_20
            apply False.elim assump_20
          let assump_19 := assump_6 assump_44
          let assump_23 := And.right assump_19
          apply False.elim assump_23
      case inr assump_11 =>
        have assump_45 : (False → False) := by
          intro assump_32
          apply False.elim assump_32
        let assump_31 := assump_6 assump_45
        let assump_35 := And.right assump_31
        apply False.elim assump_35
  let assump_4 := assump_1 assump_43
  apply False.elim assump_4


variable (p1 p3 p7 p5 p0 : Prop)
theorem file11_32324 : ((((((False ∨ p3) → (p1 → False)) → ((p5 → False) → False)) → (((p5 ∧ p3) → (True ∧ p3)) ∨ ((p7 ∧ p0) → False))) → False) → False) := by
  intro assump_10
  have assump_27 : ((((False ∨ p3) → (p1 → False)) → ((p5 → False) → False)) → (((p5 ∧ p3) → (True ∧ p3)) ∨ ((p7 ∧ p0) → False))) := by
    intro assump_14
    apply Or.inl
    intro assump_17
    apply And.intro
    apply True.intro
    cases assump_17
    case intro assump_18 assump_19 =>
      exact assump_19
  let assump_13 := assump_10 assump_27
  apply False.elim assump_13


variable (p3 p4 p0 p6 p1 : Prop)
theorem file11_32918 : (((((p6 → False) ∧ (True → False)) ∨ ((p4 → p4) → False)) → False) ∨ ((((True → p0) ∨ (p3 → p6)) → ((p1 ∨ p1) → (False → False))) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_23 : True := by
        apply True.intro
      let assump_10 := assump_5 assump_23
      apply False.elim assump_10
  case inr assump_3 =>
    have assump_24 : (p4 → p4) := by
      intro assump_17
      exact assump_17
    let assump_16 := assump_3 assump_24
    apply False.elim assump_16


variable (p1 p2 p6 p5 p4 p3 p7 : Prop)
theorem file11_33563 : (((((p1 → p4) ∨ (True → False)) ∧ ((p2 → p6) ∧ (False → False))) ∧ (((p3 ∧ p7) → (p2 → False)) ∧ ((p6 ∧ p5) ∨ (False → False)))) → ((((p3 ∧ p3) ∧ (p5 ∧ p5)) ∧ ((p5 → p3) → False)) → (((p7 ∨ p3) → False) ∨ ((p4 ∧ p4) ∧ (p3 → False))))) := by
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
            cases assump_21
            case intro assump_23 assump_24 =>
              cases assump_23
              case inl assump_25 =>
                cases assump_24
                case intro assump_29 assump_30 =>
                  cases assump_22
                  case intro assump_35 assump_36 =>
                    cases assump_36
                    case inl assump_39 =>
                      cases assump_39
                      case intro assump_41 assump_42 =>
                        apply Or.inl
                        intro assump_47
                        cases assump_47
                        case inl assump_48 =>
                          have assump_195 : (p5 → p3) := by
                            intro assump_61
                            exact assump_8
                          let assump_60 := assump_4 assump_195
                          apply False.elim assump_60
                        case inr assump_49 =>
                          have assump_196 : (p5 → p3) := by
                            intro assump_77
                            exact assump_49
                          let assump_76 := assump_4 assump_196
                          apply False.elim assump_76
                    case inr assump_40 =>
                      apply Or.inl
                      intro assump_85
                      cases assump_85
                      case inl assump_86 =>
                        have assump_197 : (p5 → p3) := by
                          intro assump_98
                          exact assump_8
                        let assump_97 := assump_4 assump_197
                        apply False.elim assump_97
                      case inr assump_87 =>
                        have assump_198 : (p5 → p3) := by
                          intro assump_113
                          exact assump_87
                        let assump_112 := assump_4 assump_198
                        apply False.elim assump_112
              case inr assump_26 =>
                cases assump_24
                case intro assump_121 assump_122 =>
                  cases assump_22
                  case intro assump_127 assump_128 =>
                    cases assump_128
                    case inl assump_131 =>
                      cases assump_131
                      case intro assump_133 assump_134 =>
                        apply Or.inl
                        intro assump_139
                        cases assump_139
                        case inl assump_140 =>
                          have assump_199 : True := by
                            apply True.intro
                          let assump_151 := assump_26 assump_199
                          apply False.elim assump_151
                        case inr assump_141 =>
                          have assump_200 : True := by
                            apply True.intro
                          let assump_163 := assump_26 assump_200
                          apply False.elim assump_163
                    case inr assump_132 =>
                      apply Or.inl
                      intro assump_169
                      cases assump_169
                      case inl assump_170 =>
                        have assump_201 : True := by
                          apply True.intro
                        let assump_180 := assump_26 assump_201
                        apply False.elim assump_180
                      case inr assump_171 =>
                        have assump_202 : True := by
                          apply True.intro
                        let assump_191 := assump_26 assump_202
                        apply False.elim assump_191


variable (p1 p4 p2 p0 p5 p3 : Prop)
theorem file11_37868 : ((((((p5 ∨ p3) → (True ∨ p1)) ∧ ((False → False) ∨ (True ∨ True))) ∨ (((p4 → False) → (p1 → False)) ∧ ((p2 → p0) ∧ (p1 → p0)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p5 ∨ p3) → (True ∨ p1)) ∧ ((False → False) ∨ (True ∨ True))) ∨ (((p4 → False) → (p1 → False)) ∧ ((p2 → p0) ∧ (p1 → p0)))) := by
    apply Or.inl
    apply And.intro
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inl
      apply True.intro
    case inr assump_7 =>
      apply Or.inl
      apply True.intro
    apply Or.inl
    intro assump_12
    apply False.elim assump_12
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p4 p2 p3 p5 p0 p1 : Prop)
theorem file11_38590 : ((((((p1 ∨ p3) ∧ (p0 ∨ p4)) → ((p5 → False) → (p2 → False))) → (((p1 → False) → False) → ((p1 → p0) ∧ (p1 → False)))) ∧ ((((True → False) → False) → ((p2 ∧ False) → (p5 → p2))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_23 : (((True → False) → False) → ((p2 ∧ False) → (p5 → p2))) := by
      intro assump_9
      intro assump_10
      intro assump_11
      cases assump_10
      case intro assump_14 assump_15 =>
        apply False.elim assump_15
    let assump_8 := assump_3 assump_23
    apply False.elim assump_8


variable (p2 p4 p5 p6 p7 p0 p3 p1 : Prop)
theorem file11_39240 : (((((False ∧ p1) ∧ (p5 → False)) ∧ ((p6 ∨ p6) → False)) → (((p0 → False) ∧ (p3 ∧ True)) ∧ ((p0 → False) ∧ (p4 ∨ p2)))) ∨ ((((p0 ∨ p6) ∨ (p7 ∨ False)) ∧ ((p3 → False) → False)) → False)) := by
  apply Or.inl
  intro assump_5
  apply And.intro
  apply And.intro
  intro assump_6
  cases assump_5
  case intro assump_9 assump_10 =>
    cases assump_9
    case intro assump_11 assump_12 =>
      cases assump_11
      case intro assump_13 assump_14 =>
        apply False.elim assump_13
  apply And.intro
  cases assump_5
  case intro assump_17 assump_18 =>
    cases assump_17
    case intro assump_19 assump_20 =>
      cases assump_19
      case intro assump_21 assump_22 =>
        apply False.elim assump_21
  apply True.intro
  apply And.intro
  intro assump_25
  cases assump_5
  case intro assump_28 assump_29 =>
    cases assump_28
    case intro assump_30 assump_31 =>
      cases assump_30
      case intro assump_32 assump_33 =>
        apply False.elim assump_32
  cases assump_5
  case intro assump_36 assump_37 =>
    cases assump_36
    case intro assump_38 assump_39 =>
      cases assump_38
      case intro assump_40 assump_41 =>
        apply False.elim assump_40


variable (p1 p5 p6 : Prop)
theorem file11_40471 : ((((((p6 ∧ False) ∧ (p1 → p6)) → False) ∨ (((True ∨ p6) → False) ∨ ((p1 ∧ p5) → False))) → False) → False) := by
  intro assump_5
  have assump_21 : ((((p6 ∧ False) ∧ (p1 → p6)) → False) ∨ (((True ∨ p6) → False) ∨ ((p1 ∧ p5) → False))) := by
    apply Or.inl
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        apply False.elim assump_13
  let assump_8 := assump_5 assump_21
  apply False.elim assump_8


variable (p2 p1 p5 p6 : Prop)
theorem file11_41022 : ((((((p5 ∨ p2) → False) → ((False → p6) ∨ (p1 → False))) ∨ (((False → False) → (False → False)) → False)) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p5 ∨ p2) → False) → ((False → p6) ∨ (p1 → False))) ∨ (((False → False) → (False → False)) → False)) := by
    apply Or.inl
    intro assump_5
    apply Or.inl
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p5 p2 p0 p3 p6 p7 : Prop)
theorem file11_41525 : (((((p7 → False) → (True ∨ p5)) ∨ ((p6 ∧ p2) → False)) ∧ (((p3 ∨ p2) ∧ (False ∨ False)) ∧ ((False → p0) ∧ (True ∨ p2)))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case inl assump_8 =>
      cases assump_7
      case intro assump_12 assump_13 =>
        cases assump_12
        case intro assump_14 assump_15 =>
          cases assump_14
          case inl assump_16 =>
            cases assump_15
            case inl assump_20 =>
              apply False.elim assump_20
            case inr assump_21 =>
              apply False.elim assump_21
          case inr assump_17 =>
            cases assump_15
            case inl assump_28 =>
              apply False.elim assump_28
            case inr assump_29 =>
              apply False.elim assump_29
    case inr assump_9 =>
      cases assump_7
      case intro assump_36 assump_37 =>
        cases assump_36
        case intro assump_38 assump_39 =>
          cases assump_38
          case inl assump_40 =>
            cases assump_39
            case inl assump_44 =>
              apply False.elim assump_44
            case inr assump_45 =>
              apply False.elim assump_45
          case inr assump_41 =>
            cases assump_39
            case inl assump_52 =>
              apply False.elim assump_52
            case inr assump_53 =>
              apply False.elim assump_53


variable (p4 p0 p1 p6 p5 p3 p2 : Prop)
theorem file11_43007 : (((((p0 → p3) → False) → ((False → False) → False)) → (((p3 ∧ p4) → (p3 ∨ p6)) → ((False → p3) ∨ (p3 ∧ p4)))) ∨ ((((p6 ∨ True) → (True ∧ p3)) → ((p5 ∧ p1) ∧ (p2 ∧ p2))) → (((p2 → p3) ∨ (True → p3)) ∧ ((p6 ∨ p5) ∧ (True ∨ p3))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  apply False.elim assump_7


variable (p7 p4 p2 p3 p5 p6 p0 : Prop)
theorem file11_43414 : (((((p5 ∨ p5) ∨ (True ∨ p2)) ∨ ((p2 → p3) ∨ (p7 ∧ True))) ∨ (((p5 → p7) → (False ∨ p7)) → ((p0 ∧ p7) ∨ (True → True)))) ∨ ((((p0 ∧ p2) → False) → False) ∨ (((p5 ∧ True) → (p5 → False)) ∨ ((p3 ∧ p4) → (p6 → p7))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inr
  apply Or.inl
  apply True.intro


variable (p1 p4 p7 p3 p6 : Prop)
theorem file11_43785 : ((((((p3 ∧ p1) ∧ (p7 ∨ p3)) ∧ ((p1 ∧ p4) → False)) → (((p4 → p4) ∧ (False ∨ True)) ∨ ((p1 ∨ p1) → (p4 ∨ p6)))) → False) → False) := by
  intro assump_1
  have assump_35 : ((((p3 ∧ p1) ∧ (p7 ∨ p3)) ∧ ((p1 ∧ p4) → False)) → (((p4 → p4) ∧ (False ∨ True)) ∨ ((p1 ∨ p1) → (p4 ∨ p6)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_9
          case inl assump_16 =>
            apply Or.inl
            apply And.intro
            intro assump_22
            exact assump_22
            apply Or.inr
            apply True.intro
          case inr assump_17 =>
            apply Or.inl
            apply And.intro
            intro assump_29
            exact assump_29
            apply Or.inr
            apply True.intro
  let assump_4 := assump_1 assump_35
  apply False.elim assump_4


variable (p0 p1 p3 p7 p4 : Prop)
theorem file11_44806 : ((((((p3 ∧ False) → False) ∧ ((p1 ∧ p7) ∨ (True → False))) ∧ (((p3 → False) ∨ (p3 → False)) ∧ ((p4 ∧ p4) → False))) ∧ ((((p3 → False) → False) ∧ ((p1 ∧ p0) ∧ (p3 ∨ p1))) ∧ (((p4 ∧ False) → False) ∧ ((True → False) ∧ (p0 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case inl assump_10 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            cases assump_5
            case intro assump_18 assump_19 =>
              cases assump_18
              case inl assump_20 =>
                cases assump_3
                case intro assump_26 assump_27 =>
                  cases assump_26
                  case intro assump_28 assump_29 =>
                    cases assump_29
                    case intro assump_32 assump_33 =>
                      cases assump_32
                      case intro assump_34 assump_35 =>
                        cases assump_33
                        case inl assump_40 =>
                          cases assump_27
                          case intro assump_44 assump_45 =>
                            cases assump_45
                            case intro assump_48 assump_49 =>
                              have assump_236 : p0 := by
                                exact assump_35
                              let assump_54 := assump_49 assump_236
                              apply False.elim assump_54
                        case inr assump_41 =>
                          cases assump_27
                          case intro assump_60 assump_61 =>
                            cases assump_61
                            case intro assump_64 assump_65 =>
                              have assump_237 : p0 := by
                                exact assump_35
                              let assump_70 := assump_65 assump_237
                              apply False.elim assump_70
              case inr assump_21 =>
                cases assump_3
                case intro assump_78 assump_79 =>
                  cases assump_78
                  case intro assump_80 assump_81 =>
                    cases assump_81
                    case intro assump_84 assump_85 =>
                      cases assump_84
                      case intro assump_86 assump_87 =>
                        cases assump_85
                        case inl assump_92 =>
                          cases assump_79
                          case intro assump_96 assump_97 =>
                            cases assump_97
                            case intro assump_100 assump_101 =>
                              have assump_238 : p0 := by
                                exact assump_87
                              let assump_106 := assump_101 assump_238
                              apply False.elim assump_106
                        case inr assump_93 =>
                          cases assump_79
                          case intro assump_112 assump_113 =>
                            cases assump_113
                            case intro assump_116 assump_117 =>
                              have assump_239 : p0 := by
                                exact assump_87
                              let assump_122 := assump_117 assump_239
                              apply False.elim assump_122
        case inr assump_11 =>
          cases assump_5
          case intro assump_128 assump_129 =>
            cases assump_128
            case inl assump_130 =>
              cases assump_3
              case intro assump_136 assump_137 =>
                cases assump_136
                case intro assump_138 assump_139 =>
                  cases assump_139
                  case intro assump_142 assump_143 =>
                    cases assump_142
                    case intro assump_144 assump_145 =>
                      cases assump_143
                      case inl assump_150 =>
                        cases assump_137
                        case intro assump_154 assump_155 =>
                          cases assump_155
                          case intro assump_158 assump_159 =>
                            have assump_240 : p0 := by
                              exact assump_145
                            let assump_164 := assump_159 assump_240
                            apply False.elim assump_164
                      case inr assump_151 =>
                        cases assump_137
                        case intro assump_170 assump_171 =>
                          cases assump_171
                          case intro assump_174 assump_175 =>
                            have assump_241 : p0 := by
                              exact assump_145
                            let assump_180 := assump_175 assump_241
                            apply False.elim assump_180
            case inr assump_131 =>
              cases assump_3
              case intro assump_188 assump_189 =>
                cases assump_188
                case intro assump_190 assump_191 =>
                  cases assump_191
                  case intro assump_194 assump_195 =>
                    cases assump_194
                    case intro assump_196 assump_197 =>
                      cases assump_195
                      case inl assump_202 =>
                        cases assump_189
                        case intro assump_206 assump_207 =>
                          cases assump_207
                          case intro assump_210 assump_211 =>
                            have assump_242 : p0 := by
                              exact assump_197
                            let assump_216 := assump_211 assump_242
                            apply False.elim assump_216
                      case inr assump_203 =>
                        cases assump_189
                        case intro assump_222 assump_223 =>
                          cases assump_223
                          case intro assump_226 assump_227 =>
                            have assump_243 : p0 := by
                              exact assump_197
                            let assump_232 := assump_227 assump_243
                            apply False.elim assump_232


variable (p6 p7 p1 : Prop)
theorem file11_51194 : (((((p6 → False) → (p1 ∨ True)) ∨ ((False → False) ∨ (p7 ∧ p1))) → False) → False) := by
  intro assump_1
  have assump_11 : (((p6 → False) → (p1 ∨ True)) ∨ ((False → False) ∨ (p7 ∧ p1))) := by
    apply Or.inl
    intro assump_5
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p4 p5 p2 p7 p0 p6 : Prop)
theorem file11_51587 : (((((p6 ∧ False) → (p5 ∨ p2)) ∨ ((p5 → False) → (p4 → False))) ∨ (((False ∨ p7) → (p0 ∧ p6)) ∧ ((True → False) → False))) ∨ ((((False → False) → (p6 ∨ p4)) ∨ ((False → False) ∧ (p4 → False))) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply False.elim assump_3


variable (p1 p2 p7 p5 p6 : Prop)
theorem file11_51995 : ((((((True → False) ∧ (p1 → p5)) → False) ∨ (((p6 → False) ∧ (p2 ∨ False)) ∧ ((False ∨ p2) ∧ (p7 ∨ True)))) → False) → False) := by
  intro assump_1
  have assump_20 : ((((True → False) ∧ (p1 → p5)) → False) ∨ (((p6 → False) ∧ (p2 ∨ False)) ∧ ((False ∨ p2) ∧ (p7 ∨ True)))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_21 : True := by
        apply True.intro
      let assump_13 := assump_6 assump_21
      apply False.elim assump_13
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p7 p4 p1 p2 p3 p0 p6 : Prop)
theorem file11_52628 : ((((((p7 ∧ p0) ∧ (p3 ∨ p7)) → False) ∧ (((p2 → False) ∧ (p3 → False)) ∧ ((p0 ∨ True) → (True ∧ p1)))) ∧ ((((False → p4) ∧ (p0 → p0)) → ((p2 → False) ∧ (p1 → False))) ∧ (((False ∨ False) ∧ (p2 ∧ p6)) ∧ ((p1 ∧ p0) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_3
          case intro assump_18 assump_19 =>
            cases assump_19
            case intro assump_22 assump_23 =>
              cases assump_22
              case intro assump_24 assump_25 =>
                cases assump_24
                case inl assump_26 =>
                  apply False.elim assump_26
                case inr assump_27 =>
                  apply False.elim assump_27


variable (p1 p7 p0 p3 p6 p4 p2 : Prop)
theorem file11_53596 : ((((((p6 ∨ p2) → False) ∨ ((p7 → False) ∨ (p1 ∨ p3))) → False) ∧ ((((p3 → False) ∨ (p6 → False)) → ((p0 → False) ∨ (p7 → False))) ∧ (((p0 → False) ∧ (p0 ∨ p7)) ∧ ((p0 → p4) ∧ (True → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_13
          case inl assump_16 =>
            cases assump_11
            case intro assump_20 assump_21 =>
              have assump_42 : True := by
                apply True.intro
              let assump_26 := assump_21 assump_42
              apply False.elim assump_26
          case inr assump_17 =>
            cases assump_11
            case intro assump_32 assump_33 =>
              have assump_43 : True := by
                apply True.intro
              let assump_38 := assump_33 assump_43
              apply False.elim assump_38


variable (p2 p7 p0 p3 p5 p4 : Prop)
theorem file11_54687 : (((((False ∧ p3) → False) ∨ ((True ∨ p7) → False)) → False) → ((((p2 → True) ∨ (p0 ∧ True)) ∨ ((p4 → False) ∧ (p5 ∧ p2))) → (((p5 ∨ p0) → False) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    cases assump_6
    case inl assump_8 =>
      have assump_61 : (((False ∧ p3) → False) ∨ ((True ∨ p7) → False)) := by
        apply Or.inl
        intro assump_15
        cases assump_15
        case intro assump_16 assump_17 =>
          apply False.elim assump_16
      let assump_14 := assump_1 assump_61
      apply False.elim assump_14
    case inr assump_9 =>
      cases assump_9
      case intro assump_23 assump_24 =>
        have assump_62 : (((False ∧ p3) → False) ∨ ((True ∨ p7) → False)) := by
          apply Or.inl
          intro assump_32
          cases assump_32
          case intro assump_33 assump_34 =>
            apply False.elim assump_33
        let assump_31 := assump_1 assump_62
        apply False.elim assump_31
  case inr assump_7 =>
    cases assump_7
    case intro assump_40 assump_41 =>
      cases assump_41
      case intro assump_44 assump_45 =>
        have assump_63 : (((False ∧ p3) → False) ∨ ((True ∨ p7) → False)) := by
          apply Or.inl
          intro assump_53
          cases assump_53
          case intro assump_54 assump_55 =>
            apply False.elim assump_54
        let assump_52 := assump_1 assump_63
        apply False.elim assump_52


variable (p6 p2 p0 p7 p5 p3 p4 : Prop)
theorem file11_56210 : (((((False ∧ True) ∧ (p2 ∧ p7)) ∧ ((False ∧ p7) ∨ (p6 ∨ p3))) → False) ∨ ((((p4 → False) ∧ (p4 → p3)) ∨ ((p0 → p5) ∨ (p4 ∧ p0))) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        apply False.elim assump_6


variable (p4 p5 p6 p7 p1 : Prop)
theorem file11_56643 : ((((((p1 → False) → False) ∧ ((p6 ∧ p4) → (p4 ∨ True))) → False) ∧ ((((p6 → False) ∧ (p6 ∧ p1)) → ((p5 → False) ∧ (p5 ∨ p7))) → False)) → False) := by
  intro assump_24
  cases assump_24
  case intro assump_25 assump_26 =>
    have assump_71 : (((p6 → False) ∧ (p6 ∧ p1)) → ((p5 → False) ∧ (p5 ∨ p7))) := by
      intro assump_32
      apply And.intro
      intro assump_33
      cases assump_32
      case intro assump_36 assump_37 =>
        cases assump_37
        case intro assump_40 assump_41 =>
          have assump_72 : p6 := by
            exact assump_40
          let assump_48 := assump_36 assump_72
          apply False.elim assump_48
      cases assump_32
      case intro assump_52 assump_53 =>
        cases assump_53
        case intro assump_56 assump_57 =>
          have assump_73 : p6 := by
            exact assump_56
          let assump_64 := assump_52 assump_73
          apply False.elim assump_64
    let assump_31 := assump_26 assump_71
    apply False.elim assump_31


variable (p7 p0 p3 p1 p5 p6 : Prop)
theorem file11_57701 : (((((p3 ∨ p7) → (True ∨ p1)) ∧ ((False → False) → False)) → False) ∨ ((((False → True) ∨ (p6 ∧ p6)) → ((False → False) ∧ (p5 → p0))) → (((p3 ∧ p7) ∨ (p6 ∧ p5)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : (False → False) := by
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p5 p2 p4 p1 p7 : Prop)
theorem file11_58183 : (((((p1 → p2) → (p2 ∨ True)) ∨ ((False ∨ p1) ∧ (True → False))) ∨ (((False ∨ p5) → False) ∧ ((p7 → p1) ∨ (p4 ∧ p2)))) ∨ ((((p5 → p7) → False) → False) ∨ (((p2 ∧ p7) ∨ (True → p1)) → ((p4 → False) → False)))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inr
  apply True.intro


variable (p2 p0 p1 p3 p4 p7 p6 p5 : Prop)
theorem file11_58559 : ((((((p3 ∨ p7) ∨ (p7 ∧ p2)) ∧ ((p2 ∨ p1) → (True ∨ p6))) → (((p6 → p1) → False) → False)) ∧ ((((p0 ∨ True) → False) ∧ ((p7 → False) ∨ (p0 ∨ True))) ∧ (((p2 → False) ∨ (p5 → p7)) ∧ ((False ∨ p6) ∨ (False ∨ p4))))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_7
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_13
        case inl assump_16 =>
          cases assump_11
          case intro assump_20 assump_21 =>
            cases assump_20
            case inl assump_22 =>
              cases assump_21
              case inl assump_26 =>
                cases assump_26
                case inl assump_28 =>
                  apply False.elim assump_28
                case inr assump_29 =>
                  have assump_214 : (p0 ∨ True) := by
                    apply Or.inr
                    apply True.intro
                  let assump_37 := assump_12 assump_214
                  apply False.elim assump_37
              case inr assump_27 =>
                cases assump_27
                case inl assump_41 =>
                  apply False.elim assump_41
                case inr assump_42 =>
                  have assump_215 : (p0 ∨ True) := by
                    apply Or.inr
                    apply True.intro
                  let assump_50 := assump_12 assump_215
                  apply False.elim assump_50
            case inr assump_23 =>
              cases assump_21
              case inl assump_56 =>
                cases assump_56
                case inl assump_58 =>
                  apply False.elim assump_58
                case inr assump_59 =>
                  have assump_216 : (p0 ∨ True) := by
                    apply Or.inr
                    apply True.intro
                  let assump_67 := assump_12 assump_216
                  apply False.elim assump_67
              case inr assump_57 =>
                cases assump_57
                case inl assump_71 =>
                  apply False.elim assump_71
                case inr assump_72 =>
                  have assump_217 : (p0 ∨ True) := by
                    apply Or.inr
                    apply True.intro
                  let assump_80 := assump_12 assump_217
                  apply False.elim assump_80
        case inr assump_17 =>
          cases assump_17
          case inl assump_84 =>
            cases assump_11
            case intro assump_88 assump_89 =>
              cases assump_88
              case inl assump_90 =>
                cases assump_89
                case inl assump_94 =>
                  cases assump_94
                  case inl assump_96 =>
                    apply False.elim assump_96
                  case inr assump_97 =>
                    have assump_218 : (p0 ∨ True) := by
                      apply Or.inl
                      exact assump_84
                    let assump_105 := assump_12 assump_218
                    apply False.elim assump_105
                case inr assump_95 =>
                  cases assump_95
                  case inl assump_109 =>
                    apply False.elim assump_109
                  case inr assump_110 =>
                    have assump_219 : (p0 ∨ True) := by
                      apply Or.inl
                      exact assump_84
                    let assump_118 := assump_12 assump_219
                    apply False.elim assump_118
              case inr assump_91 =>
                cases assump_89
                case inl assump_124 =>
                  cases assump_124
                  case inl assump_126 =>
                    apply False.elim assump_126
                  case inr assump_127 =>
                    have assump_220 : (p0 ∨ True) := by
                      apply Or.inl
                      exact assump_84
                    let assump_135 := assump_12 assump_220
                    apply False.elim assump_135
                case inr assump_125 =>
                  cases assump_125
                  case inl assump_139 =>
                    apply False.elim assump_139
                  case inr assump_140 =>
                    have assump_221 : (p0 ∨ True) := by
                      apply Or.inl
                      exact assump_84
                    let assump_148 := assump_12 assump_221
                    apply False.elim assump_148
          case inr assump_85 =>
            cases assump_11
            case intro assump_154 assump_155 =>
              cases assump_154
              case inl assump_156 =>
                cases assump_155
                case inl assump_160 =>
                  cases assump_160
                  case inl assump_162 =>
                    apply False.elim assump_162
                  case inr assump_163 =>
                    have assump_222 : (p0 ∨ True) := by
                      apply Or.inr
                      apply True.intro
                    let assump_170 := assump_12 assump_222
                    apply False.elim assump_170
                case inr assump_161 =>
                  cases assump_161
                  case inl assump_174 =>
                    apply False.elim assump_174
                  case inr assump_175 =>
                    have assump_223 : (p0 ∨ True) := by
                      apply Or.inr
                      apply True.intro
                    let assump_182 := assump_12 assump_223
                    apply False.elim assump_182
              case inr assump_157 =>
                cases assump_155
                case inl assump_188 =>
                  cases assump_188
                  case inl assump_190 =>
                    apply False.elim assump_190
                  case inr assump_191 =>
                    have assump_224 : (p0 ∨ True) := by
                      apply Or.inr
                      apply True.intro
                    let assump_198 := assump_12 assump_224
                    apply False.elim assump_198
                case inr assump_189 =>
                  cases assump_189
                  case inl assump_202 =>
                    apply False.elim assump_202
                  case inr assump_203 =>
                    have assump_225 : (p0 ∨ True) := by
                      apply Or.inr
                      apply True.intro
                    let assump_210 := assump_12 assump_225
                    apply False.elim assump_210


variable (p6 p4 p3 p1 : Prop)
theorem file11_65088 : (((((False → p3) → False) → ((p6 ∨ p1) ∧ (p1 → p4))) → False) → False) := by
  intro assump_1
  have assump_30 : (((False → p3) → False) → ((p6 ∨ p1) ∧ (p1 → p4))) := by
    intro assump_5
    apply And.intro
    have assump_31 : (False → p3) := by
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_31
    apply False.elim assump_8
    intro assump_15
    have assump_32 : (False → p3) := by
      intro assump_21
      apply False.elim assump_21
    let assump_20 := assump_5 assump_32
    apply False.elim assump_20
  let assump_4 := assump_1 assump_30
  apply False.elim assump_4


variable (p6 p1 p5 p7 p0 p4 : Prop)
theorem file11_65770 : (((((p4 ∧ p6) → (p5 ∨ p6)) ∧ ((p6 ∨ p0) ∨ (p4 ∧ p4))) ∨ (((p4 → False) ∧ (False ∧ p0)) → False)) ∨ ((((p5 → p7) ∧ (p7 ∨ p1)) ∧ ((p6 → False) ∨ (p1 → False))) ∧ (((False ∨ p0) ∧ (False ∧ p4)) ∧ ((p0 ∨ True) ∧ (p5 ∧ False))))) := by
  apply Or.inl
  apply Or.inr
  intro assump_8
  cases assump_8
  case intro assump_9 assump_10 =>
    cases assump_10
    case intro assump_13 assump_14 =>
      apply False.elim assump_13


variable (p7 p1 p0 p6 p4 p5 : Prop)
theorem file11_66251 : ((((((False → p4) ∧ (p4 ∧ p7)) ∧ ((p5 → False) ∨ (p4 → False))) → False) ∧ ((((True → False) ∧ (p1 → p6)) → False) → (((p0 → False) → (True ∨ p6)) → ((p5 ∧ False) ∧ (p5 ∨ False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_31 : (((True → False) ∧ (p1 → p6)) → False) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        have assump_32 : True := by
          apply True.intro
        let assump_17 := assump_10 assump_32
        apply False.elim assump_17
    let assump_8 := assump_3 assump_31
    have assump_33 : ((p0 → False) → (True ∨ p6)) := by
      intro assump_22
      apply Or.inl
      apply True.intro
    let assump_21 := assump_8 assump_33
    let assump_25 := And.left assump_21
    let assump_26 := And.right assump_25
    apply False.elim assump_26


variable (p7 p2 p0 p6 p5 p3 : Prop)
theorem file11_67178 : (((((p3 → False) ∧ (p5 ∧ True)) ∧ ((p0 → False) ∨ (False ∨ p7))) → (((p2 → False) ∧ (p5 ∧ p2)) → False)) ∨ ((((p3 ∧ p5) → (p2 → False)) ∧ ((p6 ∨ p5) ∧ (p0 ∨ p2))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      cases assump_1
      case intro assump_13 assump_14 =>
        cases assump_13
        case intro assump_15 assump_16 =>
          cases assump_16
          case intro assump_19 assump_20 =>
            cases assump_14
            case inl assump_25 =>
              have assump_53 : p2 := by
                exact assump_8
              let assump_34 := assump_3 assump_53
              apply False.elim assump_34
            case inr assump_26 =>
              cases assump_26
              case inl assump_38 =>
                apply False.elim assump_38
              case inr assump_39 =>
                have assump_54 : p2 := by
                  exact assump_8
                let assump_49 := assump_3 assump_54
                apply False.elim assump_49


variable (p1 p4 p2 p7 p3 p6 p5 : Prop)
theorem file11_68345 : (((((p6 → False) ∨ (p3 ∧ p3)) ∧ ((p1 ∨ p1) → (p1 → False))) ∧ (((True ∧ p5) → (False → False)) → False)) → ((((p2 ∨ p1) ∧ (p3 ∨ p2)) ∧ ((p2 ∨ p5) ∧ (p5 → p7))) ∧ (((p6 → False) → False) → ((p4 → False) → (p1 → p4))))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        have assump_196 : ((True ∧ p5) → (False → False)) := by
          intro assump_15
          intro assump_16
          apply False.elim assump_16
        let assump_14 := assump_3 assump_196
        apply False.elim assump_14
      case inr assump_7 =>
        cases assump_7
        case intro assump_22 assump_23 =>
          have assump_197 : ((True ∧ p5) → (False → False)) := by
            intro assump_33
            intro assump_34
            apply False.elim assump_34
          let assump_32 := assump_3 assump_197
          apply False.elim assump_32
  cases assump_1
  case intro assump_40 assump_41 =>
    cases assump_40
    case intro assump_42 assump_43 =>
      cases assump_42
      case inl assump_44 =>
        have assump_198 : ((True ∧ p5) → (False → False)) := by
          intro assump_53
          intro assump_54
          apply False.elim assump_54
        let assump_52 := assump_41 assump_198
        apply False.elim assump_52
      case inr assump_45 =>
        cases assump_45
        case intro assump_60 assump_61 =>
          apply Or.inl
          exact assump_61
  apply And.intro
  cases assump_1
  case intro assump_70 assump_71 =>
    cases assump_70
    case intro assump_72 assump_73 =>
      cases assump_72
      case inl assump_74 =>
        have assump_199 : ((True ∧ p5) → (False → False)) := by
          intro assump_83
          intro assump_84
          apply False.elim assump_84
        let assump_82 := assump_71 assump_199
        apply False.elim assump_82
      case inr assump_75 =>
        cases assump_75
        case intro assump_90 assump_91 =>
          have assump_200 : ((True ∧ p5) → (False → False)) := by
            intro assump_101
            intro assump_102
            apply False.elim assump_102
          let assump_100 := assump_71 assump_200
          apply False.elim assump_100
  intro assump_108
  cases assump_1
  case intro assump_111 assump_112 =>
    cases assump_111
    case intro assump_113 assump_114 =>
      cases assump_113
      case inl assump_115 =>
        have assump_201 : ((True ∧ p5) → (False → False)) := by
          intro assump_124
          intro assump_125
          apply False.elim assump_125
        let assump_123 := assump_112 assump_201
        apply False.elim assump_123
      case inr assump_116 =>
        cases assump_116
        case intro assump_131 assump_132 =>
          have assump_202 : ((True ∧ p5) → (False → False)) := by
            intro assump_142
            intro assump_143
            apply False.elim assump_143
          let assump_141 := assump_112 assump_202
          apply False.elim assump_141
  intro assump_149
  intro assump_150
  intro assump_151
  cases assump_1
  case intro assump_158 assump_159 =>
    cases assump_158
    case intro assump_160 assump_161 =>
      cases assump_160
      case inl assump_162 =>
        have assump_203 : ((True ∧ p5) → (False → False)) := by
          intro assump_171
          intro assump_172
          apply False.elim assump_172
        let assump_170 := assump_159 assump_203
        apply False.elim assump_170
      case inr assump_163 =>
        cases assump_163
        case intro assump_178 assump_179 =>
          have assump_204 : ((True ∧ p5) → (False → False)) := by
            intro assump_189
            intro assump_190
            apply False.elim assump_190
          let assump_188 := assump_159 assump_204
          apply False.elim assump_188


variable (p2 p3 p1 p7 p0 p6 p5 : Prop)
theorem file11_72315 : (((((False → p3) → False) → ((p7 ∨ p5) → False)) → False) → ((((False → False) → False) ∨ ((p1 → p3) ∨ (p1 ∨ p6))) → (((p0 → False) → (p5 ∧ p6)) ∨ ((p5 ∨ True) ∨ (p2 → False))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    apply Or.inl
    intro assump_9
    apply And.intro
    have assump_262 : (((False → p3) → False) → ((p7 ∨ p5) → False)) := by
      intro assump_14
      intro assump_15
      cases assump_15
      case inl assump_16 =>
        have assump_263 : (False → p3) := by
          intro assump_23
          apply False.elim assump_23
        let assump_22 := assump_14 assump_263
        apply False.elim assump_22
      case inr assump_17 =>
        have assump_264 : (False → p3) := by
          intro assump_34
          apply False.elim assump_34
        let assump_33 := assump_14 assump_264
        apply False.elim assump_33
    let assump_13 := assump_1 assump_262
    apply False.elim assump_13
    have assump_265 : (((False → p3) → False) → ((p7 ∨ p5) → False)) := by
      intro assump_47
      intro assump_48
      cases assump_48
      case inl assump_49 =>
        have assump_266 : (False → p3) := by
          intro assump_56
          apply False.elim assump_56
        let assump_55 := assump_47 assump_266
        apply False.elim assump_55
      case inr assump_50 =>
        have assump_267 : (False → p3) := by
          intro assump_67
          apply False.elim assump_67
        let assump_66 := assump_47 assump_267
        apply False.elim assump_66
    let assump_46 := assump_1 assump_265
    apply False.elim assump_46
  case inr assump_4 =>
    cases assump_4
    case inl assump_76 =>
      apply Or.inl
      intro assump_82
      apply And.intro
      have assump_268 : (((False → p3) → False) → ((p7 ∨ p5) → False)) := by
        intro assump_87
        intro assump_88
        cases assump_88
        case inl assump_89 =>
          have assump_269 : (False → p3) := by
            intro assump_96
            apply False.elim assump_96
          let assump_95 := assump_87 assump_269
          apply False.elim assump_95
        case inr assump_90 =>
          have assump_270 : (False → p3) := by
            intro assump_107
            apply False.elim assump_107
          let assump_106 := assump_87 assump_270
          apply False.elim assump_106
      let assump_86 := assump_1 assump_268
      apply False.elim assump_86
      have assump_271 : (((False → p3) → False) → ((p7 ∨ p5) → False)) := by
        intro assump_120
        intro assump_121
        cases assump_121
        case inl assump_122 =>
          have assump_272 : (False → p3) := by
            intro assump_129
            apply False.elim assump_129
          let assump_128 := assump_120 assump_272
          apply False.elim assump_128
        case inr assump_123 =>
          have assump_273 : (False → p3) := by
            intro assump_140
            apply False.elim assump_140
          let assump_139 := assump_120 assump_273
          apply False.elim assump_139
      let assump_119 := assump_1 assump_271
      apply False.elim assump_119
    case inr assump_77 =>
      cases assump_77
      case inl assump_149 =>
        apply Or.inl
        intro assump_155
        apply And.intro
        have assump_274 : (((False → p3) → False) → ((p7 ∨ p5) → False)) := by
          intro assump_160
          intro assump_161
          cases assump_161
          case inl assump_162 =>
            have assump_275 : (False → p3) := by
              intro assump_169
              apply False.elim assump_169
            let assump_168 := assump_160 assump_275
            apply False.elim assump_168
          case inr assump_163 =>
            have assump_276 : (False → p3) := by
              intro assump_180
              apply False.elim assump_180
            let assump_179 := assump_160 assump_276
            apply False.elim assump_179
        let assump_159 := assump_1 assump_274
        apply False.elim assump_159
        have assump_277 : (((False → p3) → False) → ((p7 ∨ p5) → False)) := by
          intro assump_193
          intro assump_194
          cases assump_194
          case inl assump_195 =>
            have assump_278 : (False → p3) := by
              intro assump_202
              apply False.elim assump_202
            let assump_201 := assump_193 assump_278
            apply False.elim assump_201
          case inr assump_196 =>
            have assump_279 : (False → p3) := by
              intro assump_213
              apply False.elim assump_213
            let assump_212 := assump_193 assump_279
            apply False.elim assump_212
        let assump_192 := assump_1 assump_277
        apply False.elim assump_192
      case inr assump_150 =>
        apply Or.inl
        intro assump_226
        apply And.intro
        have assump_280 : (((False → p3) → False) → ((p7 ∨ p5) → False)) := by
          intro assump_231
          intro assump_232
          cases assump_232
          case inl assump_233 =>
            have assump_281 : (False → p3) := by
              intro assump_240
              apply False.elim assump_240
            let assump_239 := assump_231 assump_281
            apply False.elim assump_239
          case inr assump_234 =>
            have assump_282 : (False → p3) := by
              intro assump_251
              apply False.elim assump_251
            let assump_250 := assump_231 assump_282
            apply False.elim assump_250
        let assump_230 := assump_1 assump_280
        apply False.elim assump_230
        exact assump_150


variable (p3 p0 p6 p1 p2 p4 : Prop)
theorem file11_77981 : (((((p4 ∨ p2) ∨ (True → p1)) → False) → False) → ((((p3 ∨ p0) ∧ (p0 ∧ False)) ∧ ((p0 ∨ p3) → (p4 ∨ p6))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case inl assump_7 =>
        cases assump_6
        case intro assump_11 assump_12 =>
          apply False.elim assump_12
      case inr assump_8 =>
        cases assump_6
        case intro assump_19 assump_20 =>
          apply False.elim assump_20


variable (p3 p6 p4 p0 p2 : Prop)
theorem file11_78578 : (((((p3 → False) → False) → False) ∧ (((p2 → False) → (p6 → p2)) ∧ ((p2 → p0) ∧ (False ∧ p4)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          apply False.elim assump_14


variable (p1 p6 p0 p3 p2 p5 p7 p4 : Prop)
theorem file11_79042 : (((((p5 ∨ p1) → False) ∧ ((False → False) → False)) → (((p7 ∨ p3) → (p1 → False)) ∨ ((p2 → False) ∨ (p4 → p7)))) ∨ ((((True → False) → (p2 ∨ p6)) → ((p4 → False) ∨ (p0 ∨ p4))) ∨ (((p7 → p7) ∨ (True → p7)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    intro assump_8
    intro assump_9
    cases assump_8
    case inl assump_12 =>
      have assump_36 : (False → False) := by
        intro assump_19
        apply False.elim assump_19
      let assump_18 := assump_3 assump_36
      apply False.elim assump_18
    case inr assump_13 =>
      have assump_37 : (False → False) := by
        intro assump_30
        apply False.elim assump_30
      let assump_29 := assump_3 assump_37
      apply False.elim assump_29


variable (p2 p3 p0 p1 p7 : Prop)
theorem file11_79888 : ((((((False → p3) → False) ∧ ((p0 → p2) ∧ (p7 ∨ False))) → (((p7 → p2) → False) → ((p1 ∧ p7) ∧ (p2 → False)))) → False) → False) := by
  intro assump_1
  have assump_79 : ((((False → p3) → False) ∧ ((p0 → p2) ∧ (p7 ∨ False))) → (((p7 → p2) → False) → ((p1 ∧ p7) ∧ (p2 → False)))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    apply And.intro
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_10
      case intro assump_13 assump_14 =>
        cases assump_14
        case inl assump_17 =>
          have assump_80 : (False → p3) := by
            intro assump_24
            apply False.elim assump_24
          let assump_23 := assump_9 assump_80
          apply False.elim assump_23
        case inr assump_18 =>
          apply False.elim assump_18
    cases assump_5
    case intro assump_34 assump_35 =>
      cases assump_35
      case intro assump_38 assump_39 =>
        cases assump_39
        case inl assump_42 =>
          exact assump_42
        case inr assump_43 =>
          apply False.elim assump_43
    intro assump_48
    cases assump_5
    case intro assump_53 assump_54 =>
      cases assump_54
      case intro assump_57 assump_58 =>
        cases assump_58
        case inl assump_61 =>
          have assump_81 : (False → p3) := by
            intro assump_68
            apply False.elim assump_68
          let assump_67 := assump_53 assump_81
          apply False.elim assump_67
        case inr assump_62 =>
          apply False.elim assump_62
  let assump_4 := assump_1 assump_79
  apply False.elim assump_4


variable (p2 p5 p4 p7 p3 p1 p6 : Prop)
theorem file11_81538 : (((((p6 → False) → (p7 ∨ p2)) ∧ ((True ∧ True) → False)) → (((p4 ∨ p1) ∨ (p1 ∧ p7)) → False)) ∨ ((((p3 → False) ∧ (False → p3)) → False) ∧ (((p5 → True) → (False ∧ p2)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_1
      case intro assump_9 assump_10 =>
        have assump_47 : (True ∧ True) := by
          apply And.intro
          apply True.intro
          apply True.intro
        let assump_15 := assump_10 assump_47
        apply False.elim assump_15
    case inr assump_6 =>
      cases assump_1
      case intro assump_21 assump_22 =>
        have assump_48 : (True ∧ True) := by
          apply And.intro
          apply True.intro
          apply True.intro
        let assump_27 := assump_22 assump_48
        apply False.elim assump_27
  case inr assump_4 =>
    cases assump_4
    case intro assump_31 assump_32 =>
      cases assump_1
      case intro assump_37 assump_38 =>
        have assump_49 : (True ∧ True) := by
          apply And.intro
          apply True.intro
          apply True.intro
        let assump_43 := assump_38 assump_49
        apply False.elim assump_43


variable (p2 p3 p4 p6 p7 p0 : Prop)
theorem file11_82819 : (((((p7 ∨ True) → False) → ((False → p2) → (p3 ∨ True))) ∨ (((p2 ∨ p4) ∨ (p6 ∨ p6)) ∨ ((p0 → False) → False))) ∧ ((((p3 → False) → (p7 ∨ True)) → False) → False)) := by
  apply And.intro
  apply Or.inl
  intro assump_1
  intro assump_2
  apply Or.inr
  apply True.intro
  intro assump_7
  have assump_17 : ((p3 → False) → (p7 ∨ True)) := by
    intro assump_11
    apply Or.inr
    apply True.intro
  let assump_10 := assump_7 assump_17
  apply False.elim assump_10


variable (p3 p6 p7 p4 p0 p2 : Prop)
theorem file11_83345 : ((((((False ∨ False) ∧ (p2 ∧ p6)) → ((False ∨ p7) → False)) ∨ (((p0 ∧ p0) → (p4 → False)) → ((p3 ∧ p2) ∨ (False ∨ p7)))) → False) → False) := by
  intro assump_1
  have assump_24 : ((((False ∨ False) ∧ (p2 ∧ p6)) → ((False ∨ p7) → False)) ∨ (((p0 ∧ p0) → (p4 → False)) → ((p3 ∧ p2) ∨ (False ∨ p7)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      apply False.elim assump_7
    case inr assump_8 =>
      cases assump_5
      case intro assump_13 assump_14 =>
        cases assump_13
        case inl assump_15 =>
          apply False.elim assump_15
        case inr assump_16 =>
          apply False.elim assump_16
  let assump_4 := assump_1 assump_24
  apply False.elim assump_4


variable (p0 p2 p5 p6 p3 p4 p7 : Prop)
theorem file11_84154 : (((((p2 → p0) ∧ (p5 → False)) → False) ∧ (((p4 → False) → False) → False)) → ((((True → False) → False) ∨ ((p7 → p6) ∧ (p0 → p0))) → (((p4 → False) ∨ (p6 ∧ p3)) ∨ ((p5 → False) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      apply Or.inl
      apply Or.inl
      intro assump_13
      have assump_55 : ((p4 → False) → False) := by
        intro assump_18
        have assump_56 : p4 := by
          exact assump_13
        let assump_21 := assump_18 assump_56
        apply False.elim assump_21
      let assump_17 := assump_8 assump_55
      apply False.elim assump_17
  case inr assump_4 =>
    cases assump_4
    case intro assump_28 assump_29 =>
      cases assump_1
      case intro assump_34 assump_35 =>
        apply Or.inl
        apply Or.inl
        intro assump_40
        have assump_57 : ((p4 → False) → False) := by
          intro assump_45
          have assump_58 : p4 := by
            exact assump_40
          let assump_48 := assump_45 assump_58
          apply False.elim assump_48
        let assump_44 := assump_35 assump_57
        apply False.elim assump_44


variable (p2 p0 p4 : Prop)
theorem file11_85395 : ((((((False ∧ p0) → (p4 ∧ p2)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_24 : ((((False ∧ p0) → (p4 ∧ p2)) → False) → False) := by
    intro assump_5
    have assump_25 : ((False ∧ p0) → (p4 ∧ p2)) := by
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


variable (p6 p4 p0 p3 p1 p2 p7 : Prop)
theorem file11_86062 : ((((((p2 ∧ True) ∧ (p0 ∧ False)) ∧ ((p4 ∨ p2) ∧ (p7 → True))) → (((False → p3) ∧ (p6 ∧ p7)) ∧ ((p7 ∨ True) ∧ (True → p1)))) → False) → False) := by
  intro assump_1
  have assump_79 : ((((p2 ∧ True) ∧ (p0 ∧ False)) ∧ ((p4 ∨ p2) ∧ (p7 → True))) → (((False → p3) ∧ (p6 ∧ p7)) ∧ ((p7 ∨ True) ∧ (True → p1)))) := by
    intro assump_5
    apply And.intro
    apply And.intro
    intro assump_6
    apply False.elim assump_6
    apply And.intro
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          cases assump_12
          case intro assump_19 assump_20 =>
            apply False.elim assump_20
    cases assump_5
    case intro assump_25 assump_26 =>
      cases assump_25
      case intro assump_27 assump_28 =>
        cases assump_27
        case intro assump_29 assump_30 =>
          cases assump_28
          case intro assump_35 assump_36 =>
            apply False.elim assump_36
    apply And.intro
    cases assump_5
    case intro assump_41 assump_42 =>
      cases assump_41
      case intro assump_43 assump_44 =>
        cases assump_43
        case intro assump_45 assump_46 =>
          cases assump_44
          case intro assump_51 assump_52 =>
            apply False.elim assump_52
    intro assump_57
    cases assump_5
    case intro assump_60 assump_61 =>
      cases assump_60
      case intro assump_62 assump_63 =>
        cases assump_62
        case intro assump_64 assump_65 =>
          cases assump_63
          case intro assump_70 assump_71 =>
            apply False.elim assump_71
  let assump_4 := assump_1 assump_79
  apply False.elim assump_4


variable (p6 p1 p2 p4 p7 p3 p0 : Prop)
theorem file11_87844 : (((((p0 ∧ p4) ∧ (False ∨ False)) → False) ∨ (((p2 → p4) → (p6 ∨ p1)) → ((p6 → p0) ∧ (p2 ∧ True)))) ∨ ((((True → False) → (p2 → False)) → False) ∧ (((p7 → False) ∨ (p3 ∧ p7)) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case inl assump_10 =>
        apply False.elim assump_10
      case inr assump_11 =>
        apply False.elim assump_11


variable (p3 p5 p6 p2 p1 p4 p7 p0 : Prop)
theorem file11_88401 : (((((p1 → p2) ∧ (p0 ∧ p3)) ∧ ((p0 → p0) ∧ (p3 ∧ p7))) ∨ (((p1 → False) ∧ (p2 → p4)) → ((p3 ∨ p2) ∨ (p5 → False)))) → ((((p6 ∨ p6) ∨ (p3 → False)) → False) → (((p0 ∧ p0) ∧ (p3 ∨ p6)) → ((p4 → True) → (True ∨ p6))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_3
  case intro assump_7 assump_8 =>
    cases assump_7
    case intro assump_9 assump_10 =>
      cases assump_8
      case inl assump_15 =>
        cases assump_1
        case inl assump_21 =>
          cases assump_21
          case intro assump_23 assump_24 =>
            cases assump_23
            case intro assump_25 assump_26 =>
              cases assump_26
              case intro assump_29 assump_30 =>
                cases assump_24
                case intro assump_35 assump_36 =>
                  cases assump_36
                  case intro assump_39 assump_40 =>
                    apply Or.inl
                    apply True.intro
        case inr assump_22 =>
          apply Or.inl
          apply True.intro
      case inr assump_16 =>
        cases assump_1
        case inl assump_51 =>
          cases assump_51
          case intro assump_53 assump_54 =>
            cases assump_53
            case intro assump_55 assump_56 =>
              cases assump_56
              case intro assump_59 assump_60 =>
                cases assump_54
                case intro assump_65 assump_66 =>
                  cases assump_66
                  case intro assump_69 assump_70 =>
                    apply Or.inl
                    apply True.intro
        case inr assump_52 =>
          apply Or.inl
          apply True.intro


variable (p4 p6 p0 p2 p7 p1 p5 : Prop)
theorem file11_90123 : ((((((p5 → False) → (p4 → False)) ∧ ((p6 → p0) ∨ (p5 ∧ True))) ∧ (((False → False) ∧ (p6 → False)) ∧ ((p2 ∧ p6) ∨ (False ∧ p0)))) ∨ ((((p1 ∧ p2) → False) → False) ∧ (((p1 ∨ p1) → False) ∧ ((p0 → False) ∧ (True ∧ p7))))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case inl assump_10 =>
          cases assump_5
          case intro assump_14 assump_15 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              cases assump_15
              case inl assump_22 =>
                cases assump_22
                case intro assump_24 assump_25 =>
                  have assump_112 : p6 := by
                    exact assump_25
                  let assump_32 := assump_17 assump_112
                  apply False.elim assump_32
              case inr assump_23 =>
                cases assump_23
                case intro assump_36 assump_37 =>
                  apply False.elim assump_36
        case inr assump_11 =>
          cases assump_11
          case intro assump_40 assump_41 =>
            cases assump_5
            case intro assump_46 assump_47 =>
              cases assump_46
              case intro assump_48 assump_49 =>
                cases assump_47
                case inl assump_54 =>
                  cases assump_54
                  case intro assump_56 assump_57 =>
                    have assump_113 : p6 := by
                      exact assump_57
                    let assump_64 := assump_49 assump_113
                    apply False.elim assump_64
                case inr assump_55 =>
                  cases assump_55
                  case intro assump_68 assump_69 =>
                    apply False.elim assump_68
  case inr assump_3 =>
    cases assump_3
    case intro assump_72 assump_73 =>
      cases assump_73
      case intro assump_76 assump_77 =>
        cases assump_77
        case intro assump_80 assump_81 =>
          cases assump_81
          case intro assump_84 assump_85 =>
            have assump_114 : ((p1 ∧ p2) → False) := by
              intro assump_94
              cases assump_94
              case intro assump_95 assump_96 =>
                have assump_115 : (p1 ∨ p1) := by
                  apply Or.inl
                  exact assump_95
                let assump_105 := assump_76 assump_115
                apply False.elim assump_105
            let assump_93 := assump_72 assump_114
            apply False.elim assump_93


variable (p7 p0 p5 : Prop)
theorem file11_92782 : ((((((p0 ∧ p0) → False) ∧ ((p7 → True) → False)) → False) → ((((True → False) ∧ (False → p5)) → False) → False)) → False) := by
  intro assump_1
  have assump_33 : ((((p0 ∧ p0) → False) ∧ ((p7 → True) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_34 : (p7 → True) := by
        intro assump_13
        apply True.intro
      let assump_12 := assump_7 assump_34
      apply False.elim assump_12
  let assump_4 := assump_1 assump_33
  have assump_35 : (((True → False) ∧ (False → p5)) → False) := by
    intro assump_18
    cases assump_18
    case intro assump_19 assump_20 =>
      have assump_36 : True := by
        apply True.intro
      let assump_26 := assump_19 assump_36
      apply False.elim assump_26
  let assump_17 := assump_4 assump_35
  apply False.elim assump_17


variable (p0 p7 p4 p5 : Prop)
theorem file11_93685 : ((((((False → False) → False) → False) ∨ (((True → p0) → (p7 → False)) ∧ ((p7 → False) ∨ (p5 ∧ p4)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((False → False) → False) → False) ∨ (((True → p0) → (p7 → False)) ∧ ((p7 → False) ∨ (p5 ∧ p4)))) := by
    apply Or.inl
    intro assump_5
    have assump_19 : (False → False) := by
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p0 p6 : Prop)
theorem file11_94267 : ((((((p6 ∨ p0) → (False → False)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p6 ∨ p0) → (False → False)) → False) → False) := by
    intro assump_5
    have assump_20 : ((p6 ∨ p0) → (False → False)) := by
      intro assump_9
      intro assump_10
      apply False.elim assump_10
    let assump_8 := assump_5 assump_20
    apply False.elim assump_8
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p2 p5 p4 p1 p3 p6 : Prop)
theorem file11_94781 : ((((((p5 ∧ False) ∨ (p1 ∧ True)) ∨ ((p4 ∨ p6) ∨ (p5 ∧ p3))) ∨ (((p2 ∨ p4) ∧ (p6 ∧ p2)) → False)) → False) → False) := by
  intro assump_1
  have assump_43 : ((((p5 ∧ False) ∨ (p1 ∧ True)) ∨ ((p4 ∨ p6) ∨ (p5 ∧ p3))) ∨ (((p2 ∨ p4) ∧ (p6 ∧ p2)) → False)) := by
    apply Or.inr
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case intro assump_12 assump_13 =>
          have assump_44 : ((((p5 ∧ False) ∨ (p1 ∧ True)) ∨ ((p4 ∨ p6) ∨ (p5 ∧ p3))) ∨ (((p2 ∨ p4) ∧ (p6 ∧ p2)) → False)) := by
            apply Or.inl
            apply Or.inr
            apply Or.inl
            apply Or.inr
            exact assump_12
          let assump_21 := assump_1 assump_44
          apply False.elim assump_21
      case inr assump_9 =>
        cases assump_7
        case intro assump_27 assump_28 =>
          have assump_45 : ((((p5 ∧ False) ∨ (p1 ∧ True)) ∨ ((p4 ∨ p6) ∨ (p5 ∧ p3))) ∨ (((p2 ∨ p4) ∧ (p6 ∧ p2)) → False)) := by
            apply Or.inl
            apply Or.inr
            apply Or.inl
            apply Or.inl
            exact assump_9
          let assump_36 := assump_1 assump_45
          apply False.elim assump_36
  let assump_4 := assump_1 assump_43
  apply False.elim assump_4


variable (p6 p7 p2 p1 p3 p5 p4 : Prop)
theorem file11_96140 : (((((p4 ∧ False) ∧ (False ∨ p2)) → ((p2 ∧ p3) → (p7 ∨ p1))) → False) → ((((True ∧ p6) ∧ (p4 ∧ p5)) ∨ ((p3 ∧ p6) ∨ (True → False))) ∨ (((False → p2) ∨ (p4 ∧ p1)) ∨ ((p7 ∧ False) → (p1 → False))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inr
  apply Or.inr
  intro assump_4
  have assump_27 : (((p4 ∧ False) ∧ (False ∨ p2)) → ((p2 ∧ p3) → (p7 ∨ p1))) := by
    intro assump_8
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      cases assump_8
      case intro assump_16 assump_17 =>
        cases assump_16
        case intro assump_18 assump_19 =>
          apply False.elim assump_19
  let assump_7 := assump_1 assump_27
  apply False.elim assump_7


variable (p6 p3 p2 p0 p1 p5 : Prop)
theorem file11_96888 : (((((p1 → False) → False) → ((p1 → False) → False)) ∨ (((True ∨ p5) → False) → False)) → ((((False ∨ True) ∨ (p3 → p0)) ∨ ((p6 → False) → (p2 ∧ p0))) ∨ (((p1 → True) ∧ (False → False)) → False))) := by
  intro assump_11
  cases assump_11
  case inl assump_12 =>
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply True.intro
  case inr assump_13 =>
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply True.intro


variable (p1 p2 p7 p0 p3 p5 p4 p6 : Prop)
theorem file11_97418 : (((((p0 ∧ p1) → (p6 ∧ p5)) → ((p7 ∨ p6) ∧ (p0 ∧ p7))) ∧ (((p0 → False) ∨ (p5 ∧ p6)) → False)) → ((((p1 ∧ False) ∧ (p3 → False)) ∧ ((p1 ∧ False) → False)) → (((p4 ∨ p5) ∧ (p0 → False)) ∨ ((p0 → False) → (p2 → False))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        apply False.elim assump_8


variable (p2 p4 p1 p3 p6 p5 p7 p0 : Prop)
theorem file11_97942 : ((((((True → p3) ∧ (p6 ∨ p7)) ∧ ((False ∨ p5) ∧ (p2 ∧ p0))) ∨ (((p5 → p7) ∨ (p0 → p6)) → ((p4 → False) → False))) ∧ ((((p6 → False) → (p3 → p3)) ∨ ((p5 ∨ False) → False)) ∧ (((p3 → False) → (False → p1)) → False))) → False) := by
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
          case inl assump_12 =>
            cases assump_7
            case intro assump_16 assump_17 =>
              cases assump_16
              case inl assump_18 =>
                apply False.elim assump_18
              case inr assump_19 =>
                cases assump_17
                case intro assump_24 assump_25 =>
                  cases assump_3
                  case intro assump_30 assump_31 =>
                    cases assump_30
                    case inl assump_32 =>
                      have assump_132 : ((p3 → False) → (False → p1)) := by
                        intro assump_39
                        intro assump_40
                        apply False.elim assump_40
                      let assump_38 := assump_31 assump_132
                      apply False.elim assump_38
                    case inr assump_33 =>
                      have assump_133 : ((p3 → False) → (False → p1)) := by
                        intro assump_51
                        intro assump_52
                        apply False.elim assump_52
                      let assump_50 := assump_31 assump_133
                      apply False.elim assump_50
          case inr assump_13 =>
            cases assump_7
            case intro assump_60 assump_61 =>
              cases assump_60
              case inl assump_62 =>
                apply False.elim assump_62
              case inr assump_63 =>
                cases assump_61
                case intro assump_68 assump_69 =>
                  cases assump_3
                  case intro assump_74 assump_75 =>
                    cases assump_74
                    case inl assump_76 =>
                      have assump_134 : ((p3 → False) → (False → p1)) := by
                        intro assump_83
                        intro assump_84
                        apply False.elim assump_84
                      let assump_82 := assump_75 assump_134
                      apply False.elim assump_82
                    case inr assump_77 =>
                      have assump_135 : ((p3 → False) → (False → p1)) := by
                        intro assump_95
                        intro assump_96
                        apply False.elim assump_96
                      let assump_94 := assump_75 assump_135
                      apply False.elim assump_94
    case inr assump_5 =>
      cases assump_3
      case intro assump_104 assump_105 =>
        cases assump_104
        case inl assump_106 =>
          have assump_136 : ((p3 → False) → (False → p1)) := by
            intro assump_113
            intro assump_114
            apply False.elim assump_114
          let assump_112 := assump_105 assump_136
          apply False.elim assump_112
        case inr assump_107 =>
          have assump_137 : ((p3 → False) → (False → p1)) := by
            intro assump_125
            intro assump_126
            apply False.elim assump_126
          let assump_124 := assump_105 assump_137
          apply False.elim assump_124


variable (p0 p2 p5 p6 p1 p4 : Prop)
theorem file11_101504 : (((((p2 ∧ p4) → (True → True)) ∨ ((p6 ∧ p2) ∨ (p2 ∨ p1))) ∨ (((p2 → p4) ∨ (False ∧ p4)) → ((p6 → False) ∨ (p5 → False)))) ∨ ((((p2 ∧ True) → False) → ((p5 → False) → (p1 → False))) ∨ (((p1 ∧ p6) ∧ (False ∧ True)) ∨ ((True → p6) ∨ (p5 ∧ p0))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  apply True.intro


variable (p3 p1 p5 p2 p7 p4 : Prop)
theorem file11_101912 : ((((((p5 → False) ∨ (p7 ∧ p1)) ∧ ((p7 ∨ p4) → False)) → (((p5 → False) ∧ (p4 ∨ False)) → ((True → False) → False))) ∧ ((((p4 ∨ p3) → (p7 → False)) → False) ∧ (((p5 → p5) → False) ∧ ((p4 ∧ p2) → (p3 → p7))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        have assump_24 : (p5 → p5) := by
          intro assump_18
          exact assump_18
        let assump_17 := assump_10 assump_24
        apply False.elim assump_17


variable (p1 p7 p5 p4 : Prop)
theorem file11_102546 : (((((p1 ∨ p4) ∨ (p7 → p5)) → ((p4 ∧ p5) → (p1 → p5))) → False) → False) := by
  intro assump_1
  have assump_29 : (((p1 ∨ p4) ∨ (p7 → p5)) → ((p4 ∧ p5) → (p1 → p5))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      cases assump_5
      case inl assump_16 =>
        cases assump_16
        case inl assump_18 =>
          exact assump_11
        case inr assump_19 =>
          exact assump_11
      case inr assump_17 =>
        exact assump_11
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p2 p3 p6 p0 p7 : Prop)
theorem file11_103191 : ((((((False → False) → False) → ((p0 → p3) → False)) → False) ∨ ((((p7 ∨ p6) ∨ (p3 ∧ p0)) → ((p2 ∧ p0) → (False → p7))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_34 : (((False → False) → False) → ((p0 → p3) → False)) := by
      intro assump_7
      intro assump_8
      have assump_35 : (False → False) := by
        intro assump_14
        apply False.elim assump_14
      let assump_13 := assump_7 assump_35
      apply False.elim assump_13
    let assump_6 := assump_2 assump_34
    apply False.elim assump_6
  case inr assump_3 =>
    have assump_36 : (((p7 ∨ p6) ∨ (p3 ∧ p0)) → ((p2 ∧ p0) → (False → p7))) := by
      intro assump_26
      intro assump_27
      intro assump_28
      apply False.elim assump_28
    let assump_25 := assump_3 assump_36
    apply False.elim assump_25


variable (p1 p7 p2 p0 p4 p6 p5 : Prop)
theorem file11_104098 : (((((p5 → False) → False) → ((p1 → False) → (True ∨ p4))) ∨ (((p4 → False) → False) ∨ ((p7 → False) ∧ (p4 ∧ False)))) ∨ ((((p7 ∨ p4) ∧ (False → False)) ∧ ((p6 ∧ p1) ∨ (p2 ∧ p0))) ∧ (((p5 ∨ False) ∨ (p0 → p4)) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  apply Or.inl
  apply True.intro


variable (p5 p1 p3 p7 p4 p2 p0 : Prop)
theorem file11_104485 : ((((((False ∧ False) ∧ (p7 → False)) ∨ ((p3 ∨ p4) ∨ (False → True))) ∨ (((p2 → False) → (True → False)) → ((p1 ∧ p0) → (p5 → p4)))) → False) → False) := by
  intro assump_1
  have assump_9 : ((((False ∧ False) ∧ (p7 → False)) ∨ ((p3 ∨ p4) ∨ (False → True))) ∨ (((p2 → False) → (True → False)) → ((p1 ∧ p0) → (p5 → p4)))) := by
    apply Or.inl
    apply Or.inr
    apply Or.inr
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_9
  apply False.elim assump_4


variable (p2 p1 p6 p3 : Prop)
theorem file11_105021 : ((((((p1 → p6) → (p1 → p3)) → False) → (((True ∧ True) ∨ (p2 → False)) → ((False ∨ p3) → (True ∨ p2)))) → False) → False) := by
  intro assump_1
  have assump_31 : ((((p1 → p6) → (p1 → p3)) → False) → (((True ∧ True) ∨ (p2 → False)) → ((False ∨ p3) → (True ∨ p2)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_7
    case inl assump_8 =>
      apply False.elim assump_8
    case inr assump_9 =>
      cases assump_6
      case inl assump_14 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          apply Or.inl
          apply True.intro
      case inr assump_15 =>
        apply Or.inl
        apply True.intro
  let assump_4 := assump_1 assump_31
  apply False.elim assump_4


variable (p4 p6 p3 p5 p2 p1 p7 : Prop)
theorem file11_105818 : ((((((p5 → False) ∨ (p2 → p7)) ∧ ((p4 ∨ p1) → False)) ∧ (((p4 → False) ∧ (p1 → p7)) ∨ ((p7 → False) ∧ (p2 ∨ True)))) ∧ ((((p6 → p5) → (False → False)) → False) ∧ (((p3 ∧ p4) ∧ (p3 ∨ p3)) → False))) → False) := by
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    cases assump_8
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_12
        case inl assump_14 =>
          cases assump_11
          case inl assump_20 =>
            cases assump_20
            case intro assump_22 assump_23 =>
              cases assump_9
              case intro assump_28 assump_29 =>
                have assump_150 : ((p6 → p5) → (False → False)) := by
                  intro assump_36
                  intro assump_37
                  apply False.elim assump_37
                let assump_35 := assump_28 assump_150
                apply False.elim assump_35
          case inr assump_21 =>
            cases assump_21
            case intro assump_43 assump_44 =>
              cases assump_44
              case inl assump_47 =>
                cases assump_9
                case intro assump_51 assump_52 =>
                  have assump_151 : ((p6 → p5) → (False → False)) := by
                    intro assump_59
                    intro assump_60
                    apply False.elim assump_60
                  let assump_58 := assump_51 assump_151
                  apply False.elim assump_58
              case inr assump_48 =>
                cases assump_9
                case intro assump_68 assump_69 =>
                  have assump_152 : ((p6 → p5) → (False → False)) := by
                    intro assump_76
                    intro assump_77
                    apply False.elim assump_77
                  let assump_75 := assump_68 assump_152
                  apply False.elim assump_75
        case inr assump_15 =>
          cases assump_11
          case inl assump_87 =>
            cases assump_87
            case intro assump_89 assump_90 =>
              cases assump_9
              case intro assump_95 assump_96 =>
                have assump_153 : ((p6 → p5) → (False → False)) := by
                  intro assump_103
                  intro assump_104
                  apply False.elim assump_104
                let assump_102 := assump_95 assump_153
                apply False.elim assump_102
          case inr assump_88 =>
            cases assump_88
            case intro assump_110 assump_111 =>
              cases assump_111
              case inl assump_114 =>
                cases assump_9
                case intro assump_118 assump_119 =>
                  have assump_154 : ((p6 → p5) → (False → False)) := by
                    intro assump_126
                    intro assump_127
                    apply False.elim assump_127
                  let assump_125 := assump_118 assump_154
                  apply False.elim assump_125
              case inr assump_115 =>
                cases assump_9
                case intro assump_135 assump_136 =>
                  have assump_155 : ((p6 → p5) → (False → False)) := by
                    intro assump_143
                    intro assump_144
                    apply False.elim assump_144
                  let assump_142 := assump_135 assump_155
                  apply False.elim assump_142


variable (p6 p7 p3 p1 p2 p0 p5 : Prop)
theorem file11_109277 : ((((((p2 ∧ p5) ∨ (True ∨ False)) ∨ ((p6 → False) → (p0 ∧ p1))) ∨ (((p0 → False) ∨ (p3 ∧ p3)) ∧ ((p0 → p7) → (p1 ∧ False)))) → False) → False) := by
  intro assump_1
  have assump_8 : ((((p2 ∧ p5) ∨ (True ∨ False)) ∨ ((p6 → False) → (p0 ∧ p1))) ∨ (((p0 → False) ∨ (p3 ∧ p3)) ∧ ((p0 → p7) → (p1 ∧ False)))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p2 p0 p3 p4 p6 p5 p7 : Prop)
theorem file11_109804 : (((((p6 → False) → (False → False)) ∧ ((True ∧ p6) → (p2 ∨ True))) ∨ (((p3 ∧ p7) ∨ (p2 → False)) ∨ ((p3 ∨ p0) ∨ (p5 ∧ p6)))) ∨ ((((p0 → False) → (p2 → False)) → False) ∨ (((p7 → False) → (p7 ∧ p7)) ∨ ((p4 → False) → (True → p6))))) := by
  apply Or.inl
  apply Or.inl
  apply And.intro
  intro assump_1
  intro assump_2
  apply False.elim assump_2
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    apply Or.inr
    apply True.intro


variable (p2 p6 p0 p7 p5 p4 p3 : Prop)
theorem file11_110321 : (((((p6 → False) ∨ (False ∧ p4)) → ((p3 → False) ∧ (p3 ∨ p6))) ∧ (((p2 → p4) ∧ (True → False)) ∨ ((p4 ∨ False) → (p0 ∨ p7)))) → ((((p6 ∧ False) ∧ (p6 ∨ p5)) → False) ∨ (((p7 → p7) → False) ∧ ((p7 → False) ∨ (p4 → True))))) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_7
    case inl assump_10 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        apply Or.inl
        intro assump_18
        cases assump_18
        case intro assump_19 assump_20 =>
          cases assump_19
          case intro assump_21 assump_22 =>
            apply False.elim assump_22
    case inr assump_11 =>
      apply Or.inl
      intro assump_29
      cases assump_29
      case intro assump_30 assump_31 =>
        cases assump_30
        case intro assump_32 assump_33 =>
          apply False.elim assump_33


variable (p0 p6 p3 p5 p7 p1 p2 p4 : Prop)
theorem file11_111243 : (((((p0 → p7) → (p0 ∧ p5)) → ((p0 ∧ p1) ∨ (p3 → p2))) ∨ (((p2 → p7) ∧ (True → p4)) ∨ ((p1 ∧ False) ∧ (p5 ∧ p3)))) → ((((p5 → p0) ∧ (True → False)) → ((p1 → False) → (p5 → p4))) → (((p6 → p4) ∧ (False ∧ p2)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_5
    case intro assump_8 assump_9 =>
      apply False.elim assump_8


variable (p6 p4 p3 p5 p7 p1 p2 : Prop)
theorem file11_111719 : (((((True ∧ p4) ∧ (p5 → False)) → False) ∧ (((p5 → False) ∧ (p6 → p3)) ∧ ((p3 ∧ p1) ∧ (False ∨ p5)))) → ((((p1 ∨ p6) ∧ (p4 ∧ p6)) ∧ ((True → p1) → False)) → (((p1 → False) ∨ (p2 ∨ p5)) ∧ ((p7 → True) → (True → False))))) := by
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
        case intro assump_11 assump_12 =>
          cases assump_1
          case intro assump_19 assump_20 =>
            cases assump_20
            case intro assump_23 assump_24 =>
              cases assump_23
              case intro assump_25 assump_26 =>
                cases assump_24
                case intro assump_31 assump_32 =>
                  cases assump_31
                  case intro assump_33 assump_34 =>
                    cases assump_32
                    case inl assump_39 =>
                      apply False.elim assump_39
                    case inr assump_40 =>
                      apply Or.inl
                      intro assump_45
                      have assump_209 : p5 := by
                        exact assump_40
                      let assump_54 := assump_25 assump_209
                      apply False.elim assump_54
      case inr assump_8 =>
        cases assump_6
        case intro assump_60 assump_61 =>
          cases assump_1
          case intro assump_68 assump_69 =>
            cases assump_69
            case intro assump_72 assump_73 =>
              cases assump_72
              case intro assump_74 assump_75 =>
                cases assump_73
                case intro assump_80 assump_81 =>
                  cases assump_80
                  case intro assump_82 assump_83 =>
                    cases assump_81
                    case inl assump_88 =>
                      apply False.elim assump_88
                    case inr assump_89 =>
                      apply Or.inl
                      intro assump_94
                      have assump_210 : p5 := by
                        exact assump_89
                      let assump_103 := assump_74 assump_210
                      apply False.elim assump_103
  intro assump_107
  intro assump_108
  cases assump_2
  case intro assump_113 assump_114 =>
    cases assump_113
    case intro assump_115 assump_116 =>
      cases assump_115
      case inl assump_117 =>
        cases assump_116
        case intro assump_121 assump_122 =>
          cases assump_1
          case intro assump_129 assump_130 =>
            cases assump_130
            case intro assump_133 assump_134 =>
              cases assump_133
              case intro assump_135 assump_136 =>
                cases assump_134
                case intro assump_141 assump_142 =>
                  cases assump_141
                  case intro assump_143 assump_144 =>
                    cases assump_142
                    case inl assump_149 =>
                      apply False.elim assump_149
                    case inr assump_150 =>
                      have assump_211 : p5 := by
                        exact assump_150
                      let assump_160 := assump_135 assump_211
                      apply False.elim assump_160
      case inr assump_118 =>
        cases assump_116
        case intro assump_166 assump_167 =>
          cases assump_1
          case intro assump_174 assump_175 =>
            cases assump_175
            case intro assump_178 assump_179 =>
              cases assump_178
              case intro assump_180 assump_181 =>
                cases assump_179
                case intro assump_186 assump_187 =>
                  cases assump_186
                  case intro assump_188 assump_189 =>
                    cases assump_187
                    case inl assump_194 =>
                      apply False.elim assump_194
                    case inr assump_195 =>
                      have assump_212 : p5 := by
                        exact assump_195
                      let assump_205 := assump_180 assump_212
                      apply False.elim assump_205


variable (p0 p3 p7 p1 p2 p4 p5 p6 : Prop)
theorem file11_115964 : (((((p1 → False) ∧ (p5 → False)) → ((True ∧ p6) → False)) ∧ (((p3 → False) → (p4 ∧ p7)) ∧ ((p2 ∧ p5) ∧ (True → False)))) → ((((p0 ∧ p0) ∨ (False → False)) → False) → False)) := by
  intro assump_7
  intro assump_8
  cases assump_7
  case intro assump_11 assump_12 =>
    cases assump_12
    case intro assump_15 assump_16 =>
      cases assump_16
      case intro assump_19 assump_20 =>
        cases assump_19
        case intro assump_21 assump_22 =>
          have assump_33 : True := by
            apply True.intro
          let assump_29 := assump_20 assump_33
          apply False.elim assump_29


variable (p1 p2 p0 p3 p7 p5 p4 p6 : Prop)
theorem file11_116634 : ((((((p3 ∧ p7) → (p0 ∨ p2)) ∨ ((p5 → p6) ∨ (p1 → True))) → (((p7 → False) → (False ∧ p5)) ∨ ((True → p6) ∧ (p4 → False)))) ∧ ((((p5 → False) ∨ (p7 ∧ p2)) → ((p6 ∨ False) → (True ∧ p6))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_30 : (((p5 → False) ∨ (p7 ∧ p2)) → ((p6 ∨ False) → (True ∧ p6))) := by
      intro assump_9
      intro assump_10
      apply And.intro
      apply True.intro
      cases assump_10
      case inl assump_11 =>
        cases assump_9
        case inl assump_15 =>
          exact assump_11
        case inr assump_16 =>
          cases assump_16
          case intro assump_19 assump_20 =>
            exact assump_11
      case inr assump_12 =>
        apply False.elim assump_12
    let assump_8 := assump_3 assump_30
    apply False.elim assump_8


