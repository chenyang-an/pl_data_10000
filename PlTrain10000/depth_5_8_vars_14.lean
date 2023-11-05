variable (p5 p1 p3 p6 p0 p4 p7 : Prop)
theorem file14_47 : (((((True → False) → False) ∧ ((p3 → False) → (p0 ∧ p0))) ∧ (((p5 → False) ∧ (False → p4)) → ((p6 ∧ p3) → (p4 → p0)))) → ((((p7 ∧ True) ∧ (False ∨ p3)) ∨ ((p3 ∧ p5) ∨ (p6 ∨ p4))) ∨ (((p1 → False) → False) → ((p0 ∧ p0) ∨ (True ∨ p5))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply Or.inr
      intro assump_12
      apply Or.inr
      apply Or.inl
      apply True.intro


variable (p3 p6 : Prop)
theorem file14_562 : (((((p6 → False) ∧ (p3 ∧ p6)) → False) → False) → False) := by
  intro assump_1
  have assump_25 : (((p6 → False) ∧ (p3 ∧ p6)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        have assump_26 : p6 := by
          exact assump_11
        let assump_18 := assump_6 assump_26
        apply False.elim assump_18
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p6 p7 p1 p0 p5 p2 p4 : Prop)
theorem file14_1106 : (((((True ∨ p4) ∧ (False ∨ p4)) → ((p0 → True) ∧ (p4 ∨ p7))) ∧ (((True → False) ∧ (True → p6)) ∧ ((p0 → p0) ∧ (p5 ∨ p0)))) → ((((p2 ∧ p0) → False) → False) → (((p5 → False) → (False → False)) ∨ ((p1 → p7) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_10
        case intro assump_17 assump_18 =>
          cases assump_18
          case inl assump_21 =>
            apply Or.inl
            intro assump_25
            intro assump_26
            apply False.elim assump_26
          case inr assump_22 =>
            apply Or.inl
            intro assump_31
            intro assump_32
            apply False.elim assump_32


variable (p3 p6 p2 p4 : Prop)
theorem file14_1981 : ((((((p6 → False) ∨ (p2 ∧ p3)) → False) ∨ (((p6 → False) → (False ∧ p4)) → False)) ∧ ((((p3 → False) → (True ∨ p4)) ∨ ((p2 → False) ∧ (False → p4))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_28 : (((p3 → False) → (True ∨ p4)) ∨ ((p2 → False) ∧ (False → p4))) := by
        apply Or.inl
        intro assump_11
        apply Or.inl
        apply True.intro
      let assump_10 := assump_3 assump_28
      apply False.elim assump_10
    case inr assump_5 =>
      have assump_29 : (((p3 → False) → (True ∨ p4)) ∨ ((p2 → False) ∧ (False → p4))) := by
        apply Or.inl
        intro assump_22
        apply Or.inl
        apply True.intro
      let assump_21 := assump_3 assump_29
      apply False.elim assump_21


variable (p5 p2 p1 p4 p7 p0 p3 : Prop)
theorem file14_2871 : (((((p0 ∨ False) → (p0 → p1)) → False) → (((p7 → False) → False) ∨ ((p2 → p7) → False))) → ((((p3 → p5) ∧ (True ∨ p0)) ∧ ((p4 → p1) ∧ (False ∧ False))) → (((p4 ∨ p4) ∧ (p5 ∨ p0)) ∧ ((p4 ∧ p4) ∨ (p1 ∧ p1))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  apply And.intro
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_6
      case inl assump_9 =>
        cases assump_4
        case intro assump_13 assump_14 =>
          cases assump_14
          case intro assump_17 assump_18 =>
            apply False.elim assump_17
      case inr assump_10 =>
        cases assump_4
        case intro assump_23 assump_24 =>
          cases assump_24
          case intro assump_27 assump_28 =>
            apply False.elim assump_27
  cases assump_2
  case intro assump_31 assump_32 =>
    cases assump_31
    case intro assump_33 assump_34 =>
      cases assump_34
      case inl assump_37 =>
        cases assump_32
        case intro assump_41 assump_42 =>
          cases assump_42
          case intro assump_45 assump_46 =>
            apply False.elim assump_45
      case inr assump_38 =>
        cases assump_32
        case intro assump_51 assump_52 =>
          cases assump_52
          case intro assump_55 assump_56 =>
            apply False.elim assump_55
  cases assump_2
  case intro assump_59 assump_60 =>
    cases assump_59
    case intro assump_61 assump_62 =>
      cases assump_62
      case inl assump_65 =>
        cases assump_60
        case intro assump_69 assump_70 =>
          cases assump_70
          case intro assump_73 assump_74 =>
            apply False.elim assump_73
      case inr assump_66 =>
        cases assump_60
        case intro assump_79 assump_80 =>
          cases assump_80
          case intro assump_83 assump_84 =>
            apply False.elim assump_83


variable (p0 p1 p4 p3 : Prop)
theorem file14_4817 : ((((((True ∨ False) ∨ (p1 ∨ False)) → False) → (((p4 → p0) → False) ∧ ((p3 → False) ∨ (p0 ∧ p0)))) → False) → False) := by
  intro assump_1
  have assump_28 : ((((True ∨ False) ∨ (p1 ∨ False)) → False) → (((p4 → p0) → False) ∧ ((p3 → False) ∨ (p0 ∧ p0)))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    have assump_29 : ((True ∨ False) ∨ (p1 ∨ False)) := by
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_11 := assump_5 assump_29
    apply False.elim assump_11
    apply Or.inl
    intro assump_17
    have assump_30 : ((True ∨ False) ∨ (p1 ∨ False)) := by
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_21 := assump_5 assump_30
    apply False.elim assump_21
  let assump_4 := assump_1 assump_28
  apply False.elim assump_4


variable (p0 p4 p5 p1 : Prop)
theorem file14_5675 : ((((((False → p0) ∧ (p5 ∨ p5)) ∧ ((p1 ∧ p0) ∧ (p4 ∨ p5))) → (((p4 → p4) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_100 : ((((False → p0) ∧ (p5 ∨ p5)) ∧ ((p1 ∧ p0) ∧ (p4 ∨ p5))) → (((p4 → p4) → False) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_12
        case inl assump_15 =>
          cases assump_10
          case intro assump_19 assump_20 =>
            cases assump_19
            case intro assump_21 assump_22 =>
              cases assump_20
              case inl assump_27 =>
                have assump_101 : (p4 → p4) := by
                  intro assump_37
                  exact assump_37
                let assump_36 := assump_6 assump_101
                apply False.elim assump_36
              case inr assump_28 =>
                have assump_102 : (p4 → p4) := by
                  intro assump_51
                  exact assump_51
                let assump_50 := assump_6 assump_102
                apply False.elim assump_50
        case inr assump_16 =>
          cases assump_10
          case intro assump_59 assump_60 =>
            cases assump_59
            case intro assump_61 assump_62 =>
              cases assump_60
              case inl assump_67 =>
                have assump_103 : (p4 → p4) := by
                  intro assump_77
                  exact assump_77
                let assump_76 := assump_6 assump_103
                apply False.elim assump_76
              case inr assump_68 =>
                have assump_104 : (p4 → p4) := by
                  intro assump_91
                  exact assump_91
                let assump_90 := assump_6 assump_104
                apply False.elim assump_90
  let assump_4 := assump_1 assump_100
  apply False.elim assump_4


variable (p4 p7 p1 p3 p2 p0 : Prop)
theorem file14_7635 : ((((((p1 ∧ p2) → (p0 ∧ p2)) ∨ ((p0 → p3) ∧ (p0 → False))) → (((p0 → p7) → False) ∧ ((p0 → p2) ∧ (p7 ∧ p2)))) ∧ ((((p4 → False) ∨ (p4 ∨ p4)) ∧ ((p2 → False) ∧ (p0 → p4))) ∧ (((True → False) → (p3 ∧ p2)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_9
          case intro assump_14 assump_15 =>
            have assump_95 : ((True → False) → (p3 ∧ p2)) := by
              intro assump_23
              apply And.intro
              have assump_96 : True := by
                apply True.intro
              let assump_26 := assump_23 assump_96
              apply False.elim assump_26
              have assump_97 : True := by
                apply True.intro
              let assump_32 := assump_23 assump_97
              apply False.elim assump_32
            let assump_22 := assump_7 assump_95
            apply False.elim assump_22
        case inr assump_11 =>
          cases assump_11
          case inl assump_39 =>
            cases assump_9
            case intro assump_43 assump_44 =>
              have assump_98 : ((True → False) → (p3 ∧ p2)) := by
                intro assump_52
                apply And.intro
                have assump_99 : True := by
                  apply True.intro
                let assump_55 := assump_52 assump_99
                apply False.elim assump_55
                have assump_100 : True := by
                  apply True.intro
                let assump_61 := assump_52 assump_100
                apply False.elim assump_61
              let assump_51 := assump_7 assump_98
              apply False.elim assump_51
          case inr assump_40 =>
            cases assump_9
            case intro assump_70 assump_71 =>
              have assump_101 : ((True → False) → (p3 ∧ p2)) := by
                intro assump_79
                apply And.intro
                have assump_102 : True := by
                  apply True.intro
                let assump_82 := assump_79 assump_102
                apply False.elim assump_82
                have assump_103 : True := by
                  apply True.intro
                let assump_88 := assump_79 assump_103
                apply False.elim assump_88
              let assump_78 := assump_7 assump_101
              apply False.elim assump_78


variable (p1 p5 p4 p0 p6 : Prop)
theorem file14_10185 : ((((((p0 ∧ p1) → False) → ((p1 → False) ∧ (p4 → p0))) → (((False ∧ False) → (p6 ∨ p4)) ∨ ((True → p6) ∧ (p5 ∧ p5)))) → False) → False) := by
  intro assump_1
  have assump_16 : ((((p0 ∧ p1) → False) → ((p1 → False) ∧ (p4 → p0))) → (((False ∧ False) → (p6 ∨ p4)) ∨ ((True → p6) ∧ (p5 ∧ p5)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      apply False.elim assump_9
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p0 p6 p7 p5 : Prop)
theorem file14_10745 : (((((p5 → True) → (True ∨ p0)) ∨ ((p6 ∧ True) ∨ (p7 → False))) → False) → ((((p0 → p5) ∨ (p5 ∨ p6)) ∨ ((p5 → p6) ∧ (p6 ∨ p6))) → False)) := by
  intro assump_9
  intro assump_10
  cases assump_10
  case inl assump_11 =>
    cases assump_11
    case inl assump_13 =>
      have assump_78 : (((p5 → True) → (True ∨ p0)) ∨ ((p6 ∧ True) ∨ (p7 → False))) := by
        apply Or.inl
        intro assump_20
        apply Or.inl
        apply True.intro
      let assump_19 := assump_9 assump_78
      apply False.elim assump_19
    case inr assump_14 =>
      cases assump_14
      case inl assump_26 =>
        have assump_79 : (((p5 → True) → (True ∨ p0)) ∨ ((p6 ∧ True) ∨ (p7 → False))) := by
          apply Or.inl
          intro assump_33
          apply Or.inl
          apply True.intro
        let assump_32 := assump_9 assump_79
        apply False.elim assump_32
      case inr assump_27 =>
        have assump_80 : (((p5 → True) → (True ∨ p0)) ∨ ((p6 ∧ True) ∨ (p7 → False))) := by
          apply Or.inl
          intro assump_44
          apply Or.inl
          apply True.intro
        let assump_43 := assump_9 assump_80
        apply False.elim assump_43
  case inr assump_12 =>
    cases assump_12
    case intro assump_50 assump_51 =>
      cases assump_51
      case inl assump_54 =>
        have assump_81 : (((p5 → True) → (True ∨ p0)) ∨ ((p6 ∧ True) ∨ (p7 → False))) := by
          apply Or.inl
          intro assump_61
          apply Or.inl
          apply True.intro
        let assump_60 := assump_9 assump_81
        apply False.elim assump_60
      case inr assump_55 =>
        have assump_82 : (((p5 → True) → (True ∨ p0)) ∨ ((p6 ∧ True) ∨ (p7 → False))) := by
          apply Or.inl
          intro assump_72
          apply Or.inl
          apply True.intro
        let assump_71 := assump_9 assump_82
        apply False.elim assump_71


theorem file14_12635 : (((((True → False) → False) ∧ ((True ∧ False) → False)) → False) → False) := by
  intro assump_1
  have assump_22 : (((True → False) → False) ∧ ((True ∧ False) → False)) := by
    apply And.intro
    intro assump_5
    have assump_23 : True := by
      apply True.intro
    let assump_8 := assump_5 assump_23
    apply False.elim assump_8
    intro assump_12
    cases assump_12
    case intro assump_13 assump_14 =>
      apply False.elim assump_14
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p7 p2 p5 p4 p3 p1 p0 p6 : Prop)
theorem file14_13216 : ((((((True ∨ p2) ∧ (p5 ∧ p4)) ∧ ((p6 → p3) ∧ (True → False))) → (((True ∨ p1) → (p3 → p7)) → False)) ∧ ((((True → False) → False) ∨ ((p0 ∧ p0) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : (((True → False) → False) ∨ ((p0 ∧ p0) → False)) := by
      apply Or.inl
      intro assump_9
      have assump_20 : True := by
        apply True.intro
      let assump_12 := assump_9 assump_20
      apply False.elim assump_12
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


variable (p6 p5 p3 p1 p2 p0 p4 p7 : Prop)
theorem file14_13847 : (((((p7 → True) ∧ (True ∨ p4)) → False) → (((False ∧ p2) ∧ (p7 ∧ p3)) → False)) ∨ ((((p0 → p1) ∧ (p5 ∨ False)) → ((True ∨ False) → (False ∨ False))) → (((False → True) ∨ (p6 ∧ p3)) → ((p1 → False) ∨ (False ∨ True))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      apply False.elim assump_5


variable (p0 p7 p6 p5 p1 : Prop)
theorem file14_14315 : (((((True ∨ p6) → (True → False)) → ((p7 → p0) → (p0 ∧ p0))) → False) → ((((p1 ∨ p5) → (p6 ∨ p1)) → False) → False)) := by
  intro assump_1
  intro assump_2
  have assump_31 : (((True ∨ p6) → (True → False)) → ((p7 → p0) → (p0 ∧ p0))) := by
    intro assump_8
    intro assump_9
    apply And.intro
    have assump_32 : (True ∨ p6) := by
      apply Or.inl
      apply True.intro
    let assump_14 := assump_8 assump_32
    have assump_33 : True := by
      apply True.intro
    let assump_15 := assump_14 assump_33
    apply False.elim assump_15
    have assump_34 : (True ∨ p6) := by
      apply Or.inl
      apply True.intro
    let assump_23 := assump_8 assump_34
    have assump_35 : True := by
      apply True.intro
    let assump_24 := assump_23 assump_35
    apply False.elim assump_24
  let assump_7 := assump_1 assump_31
  apply False.elim assump_7


variable (p5 p0 p6 p4 p7 p1 p3 : Prop)
theorem file14_15238 : (((((False → False) ∨ (p0 → False)) → False) → (((p6 → False) ∧ (False ∨ False)) ∨ ((p1 → False) ∧ (p5 → False)))) ∨ ((((False ∨ p6) → False) → ((p7 → p4) → (p5 ∨ p5))) ∧ (((p3 ∨ p7) ∧ (p3 ∨ p7)) ∨ ((p1 ∧ p6) ∧ (p0 → p5))))) := by
  apply Or.inl
  intro assump_1
  apply Or.inr
  apply And.intro
  intro assump_15
  have assump_37 : ((False → False) ∨ (p0 → False)) := by
    apply Or.inl
    intro assump_20
    apply False.elim assump_20
  let assump_19 := assump_1 assump_37
  apply False.elim assump_19
  intro assump_26
  have assump_38 : ((False → False) ∨ (p0 → False)) := by
    apply Or.inl
    intro assump_31
    apply False.elim assump_31
  let assump_30 := assump_1 assump_38
  apply False.elim assump_30


variable (p7 p1 p0 p6 p4 p2 : Prop)
theorem file14_16016 : (((((True ∧ p0) → False) → False) → False) → ((((p2 ∧ p1) ∧ (False ∨ False)) ∧ ((p1 → False) ∨ (False ∧ p4))) → (((p6 → False) → (p4 → False)) ∧ ((p7 ∧ p6) ∧ (p6 → False))))) := by
  intro assump_28
  intro assump_29
  apply And.intro
  intro assump_30
  intro assump_31
  cases assump_29
  case intro assump_36 assump_37 =>
    cases assump_36
    case intro assump_38 assump_39 =>
      cases assump_38
      case intro assump_40 assump_41 =>
        cases assump_39
        case inl assump_46 =>
          apply False.elim assump_46
        case inr assump_47 =>
          apply False.elim assump_47
  apply And.intro
  apply And.intro
  cases assump_29
  case intro assump_52 assump_53 =>
    cases assump_52
    case intro assump_54 assump_55 =>
      cases assump_54
      case intro assump_56 assump_57 =>
        cases assump_55
        case inl assump_62 =>
          apply False.elim assump_62
        case inr assump_63 =>
          apply False.elim assump_63
  cases assump_29
  case intro assump_68 assump_69 =>
    cases assump_68
    case intro assump_70 assump_71 =>
      cases assump_70
      case intro assump_72 assump_73 =>
        cases assump_71
        case inl assump_78 =>
          apply False.elim assump_78
        case inr assump_79 =>
          apply False.elim assump_79
  intro assump_84
  cases assump_29
  case intro assump_87 assump_88 =>
    cases assump_87
    case intro assump_89 assump_90 =>
      cases assump_89
      case intro assump_91 assump_92 =>
        cases assump_90
        case inl assump_97 =>
          apply False.elim assump_97
        case inr assump_98 =>
          apply False.elim assump_98


variable (p7 p3 p2 p0 p5 : Prop)
theorem file14_17726 : ((((((True ∨ p7) → (True ∨ False)) ∨ ((p2 ∧ p5) ∧ (p3 → False))) ∧ (((p0 → False) → (p5 → True)) ∨ ((p5 → p3) ∨ (p7 ∨ p2)))) → False) → False) := by
  intro assump_1
  have assump_17 : ((((True ∨ p7) → (True ∨ False)) ∨ ((p2 ∧ p5) ∧ (p3 → False))) ∧ (((p0 → False) → (p5 → True)) ∨ ((p5 → p3) ∨ (p7 ∨ p2)))) := by
    apply And.intro
    apply Or.inl
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
    intro assump_13
    apply True.intro
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p7 p1 p4 : Prop)
theorem file14_18443 : ((((((False → False) → False) → False) → False) ∨ ((((False ∧ p7) ∧ (True ∨ p7)) → ((False → p1) ∧ (p4 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_39 : (((False → False) → False) → False) := by
      intro assump_7
      have assump_40 : (False → False) := by
        intro assump_11
        apply False.elim assump_11
      let assump_10 := assump_7 assump_40
      apply False.elim assump_10
    let assump_6 := assump_2 assump_39
    apply False.elim assump_6
  case inr assump_3 =>
    have assump_41 : (((False ∧ p7) ∧ (True ∨ p7)) → ((False → p1) ∧ (p4 → False))) := by
      intro assump_23
      apply And.intro
      intro assump_24
      apply False.elim assump_24
      intro assump_27
      cases assump_23
      case intro assump_30 assump_31 =>
        cases assump_30
        case intro assump_32 assump_33 =>
          apply False.elim assump_32
    let assump_22 := assump_3 assump_41
    apply False.elim assump_22


variable (p0 p5 p3 p1 p7 p6 : Prop)
theorem file14_19501 : ((((((False ∧ p1) → (p3 ∨ p3)) → ((p7 → False) ∧ (p6 ∧ p0))) → (((p5 → p7) → (p7 → p7)) → ((False ∨ p5) → (p7 → False)))) → False) → False) := by
  intro assump_5
  have assump_39 : ((((False ∧ p1) → (p3 ∨ p3)) → ((p7 → False) ∧ (p6 ∧ p0))) → (((p5 → p7) → (p7 → p7)) → ((False ∨ p5) → (p7 → False)))) := by
    intro assump_9
    intro assump_10
    intro assump_11
    intro assump_12
    cases assump_11
    case inl assump_15 =>
      apply False.elim assump_15
    case inr assump_16 =>
      have assump_40 : ((False ∧ p1) → (p3 ∨ p3)) := by
        intro assump_26
        cases assump_26
        case intro assump_27 assump_28 =>
          apply False.elim assump_27
      let assump_25 := assump_9 assump_40
      let assump_31 := And.left assump_25
      have assump_41 : p7 := by
        exact assump_12
      let assump_32 := assump_31 assump_41
      apply False.elim assump_32
  let assump_8 := assump_5 assump_39
  apply False.elim assump_8


variable (p7 p3 p2 p4 p0 p1 : Prop)
theorem file14_20517 : ((((((p4 → p0) ∧ (False ∧ True)) → ((p3 ∨ True) ∨ (p4 ∧ p2))) ∨ (((p2 ∧ p7) ∨ (p4 → False)) → ((p1 ∧ True) → False))) → False) → False) := by
  intro assump_1
  have assump_17 : ((((p4 → p0) ∧ (False ∧ True)) → ((p3 ∨ True) ∨ (p4 ∧ p2))) ∨ (((p2 ∧ p7) ∨ (p4 → False)) → ((p1 ∧ True) → False))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        apply False.elim assump_10
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p1 p4 p7 : Prop)
theorem file14_21120 : ((((((p4 ∨ p1) → False) → False) → (((True → False) → False) ∨ ((p7 ∨ p1) → False))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p4 ∨ p1) → False) → False) → (((True → False) → False) ∨ ((p7 ∨ p1) → False))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    have assump_19 : True := by
      apply True.intro
    let assump_11 := assump_8 assump_19
    apply False.elim assump_11
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p2 p3 p4 p5 p6 p1 : Prop)
theorem file14_21660 : (((((p5 ∨ p3) ∨ (False → p5)) → False) → (((p1 ∧ p6) → False) → False)) ∧ ((((False ∧ p4) → (p2 ∨ True)) → False) → False)) := by
  apply And.intro
  intro assump_1
  intro assump_2
  have assump_26 : ((p5 ∨ p3) ∨ (False → p5)) := by
    apply Or.inr
    intro assump_8
    apply False.elim assump_8
  let assump_7 := assump_1 assump_26
  apply False.elim assump_7
  intro assump_14
  have assump_27 : ((False ∧ p4) → (p2 ∨ True)) := by
    intro assump_18
    cases assump_18
    case intro assump_19 assump_20 =>
      apply False.elim assump_19
  let assump_17 := assump_14 assump_27
  apply False.elim assump_17


variable (p1 p2 p3 p0 p4 : Prop)
theorem file14_22333 : ((((((True ∧ p3) → (p0 → False)) ∧ ((p2 ∨ p2) → (p4 → False))) → (((p0 → p1) → False) → ((p4 ∧ p1) → False))) → False) → False) := by
  intro assump_1
  have assump_34 : ((((True ∧ p3) → (p0 → False)) ∧ ((p2 ∨ p2) → (p4 → False))) → (((p0 → p1) → False) → ((p4 ∧ p1) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_7
    case intro assump_8 assump_9 =>
      cases assump_5
      case intro assump_16 assump_17 =>
        have assump_35 : (p0 → p1) := by
          intro assump_25
          exact assump_9
        let assump_24 := assump_6 assump_35
        apply False.elim assump_24
  let assump_4 := assump_1 assump_34
  apply False.elim assump_4


variable (p0 p1 p5 p6 p2 p4 p3 : Prop)
theorem file14_23089 : (((((p2 ∨ p1) → False) → False) → (((p0 ∧ p4) → (p0 ∨ p1)) ∨ ((p4 ∨ p1) ∨ (p3 → True)))) ∨ ((((p2 → False) ∧ (p2 → False)) → False) ∨ (((p4 ∨ p2) → (p3 ∨ True)) ∧ ((p5 → p6) → False)))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply Or.inl
    exact assump_5


variable (p0 p2 p5 p3 p4 p6 p7 p1 : Prop)
theorem file14_23498 : (((((p5 → False) ∧ (p1 ∨ p7)) → ((p1 ∨ p6) ∧ (p4 ∧ False))) ∧ (((p1 ∨ p1) → (p6 → True)) → ((False → p5) → (p2 ∧ False)))) → ((((False ∨ p2) → (p6 → p7)) → ((p0 → False) ∨ (p7 ∧ True))) → (((p4 → False) ∨ (p2 → False)) ∨ ((True → p6) → (True ∨ p3))))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    apply Or.inl
    apply Or.inl
    intro assump_11
    have assump_27 : ((p1 ∨ p1) → (p6 → True)) := by
      intro assump_16
      intro assump_17
      apply True.intro
    let assump_15 := assump_6 assump_27
    have assump_28 : (False → p5) := by
      intro assump_19
      apply False.elim assump_19
    let assump_18 := assump_15 assump_28
    let assump_22 := And.right assump_18
    apply False.elim assump_22


variable (p3 p0 p5 p2 p1 p6 : Prop)
theorem file14_24323 : (((((p5 ∨ p5) → False) → ((p1 → False) → False)) ∧ (((p3 ∧ p3) → (p3 ∨ p5)) → False)) → ((((False ∧ p1) ∧ (p6 → False)) ∨ ((p0 ∧ p2) ∧ (p6 ∨ True))) ∨ (((False → p1) → False) ∨ ((p2 ∨ p1) ∧ (p5 ∨ p1))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inr
    apply Or.inl
    intro assump_8
    have assump_23 : ((p3 ∧ p3) → (p3 ∨ p5)) := by
      intro assump_13
      cases assump_13
      case intro assump_14 assump_15 =>
        apply Or.inl
        exact assump_15
    let assump_12 := assump_3 assump_23
    apply False.elim assump_12


variable (p2 p3 p1 p5 p4 p0 : Prop)
theorem file14_24965 : ((((((p4 → False) ∨ (p5 → False)) ∨ ((p0 ∨ p3) ∧ (p2 ∧ False))) ∧ (((p3 ∧ False) → (p0 ∨ True)) ∨ ((p5 ∨ p2) ∧ (p5 → p5)))) ∧ ((((True ∧ p4) ∧ (True ∨ True)) ∨ ((True ∧ p4) → False)) → (((False → p5) → (True ∨ p1)) → False))) → False) := by
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
            have assump_222 : (((True ∧ p4) ∧ (True ∨ True)) ∨ ((True ∧ p4) → False)) := by
              apply Or.inr
              intro assump_19
              cases assump_19
              case intro assump_20 assump_21 =>
                have assump_223 : (((True ∧ p4) ∧ (True ∨ True)) ∨ ((True ∧ p4) → False)) := by
                  apply Or.inl
                  apply And.intro
                  apply And.intro
                  apply True.intro
                  exact assump_21
                  apply Or.inl
                  apply True.intro
                let assump_27 := assump_3 assump_223
                have assump_224 : ((False → p5) → (True ∨ p1)) := by
                  intro assump_29
                  apply Or.inl
                  apply True.intro
                let assump_28 := assump_27 assump_224
                apply False.elim assump_28
            let assump_18 := assump_3 assump_222
            have assump_225 : ((False → p5) → (True ∨ p1)) := by
              intro assump_36
              apply Or.inl
              apply True.intro
            let assump_35 := assump_18 assump_225
            apply False.elim assump_35
          case inr assump_13 =>
            cases assump_13
            case intro assump_42 assump_43 =>
              cases assump_42
              case inl assump_44 =>
                have assump_226 : (((True ∧ p4) ∧ (True ∨ True)) ∨ ((True ∧ p4) → False)) := by
                  apply Or.inr
                  intro assump_53
                  cases assump_53
                  case intro assump_54 assump_55 =>
                    have assump_227 : (((True ∧ p4) ∧ (True ∨ True)) ∨ ((True ∧ p4) → False)) := by
                      apply Or.inl
                      apply And.intro
                      apply And.intro
                      apply True.intro
                      exact assump_55
                      apply Or.inl
                      apply True.intro
                    let assump_61 := assump_3 assump_227
                    have assump_228 : ((False → p5) → (True ∨ p1)) := by
                      intro assump_63
                      apply Or.inl
                      apply True.intro
                    let assump_62 := assump_61 assump_228
                    apply False.elim assump_62
                let assump_52 := assump_3 assump_226
                have assump_229 : ((False → p5) → (True ∨ p1)) := by
                  intro assump_70
                  apply Or.inl
                  apply True.intro
                let assump_69 := assump_52 assump_229
                apply False.elim assump_69
              case inr assump_45 =>
                have assump_230 : (((True ∧ p4) ∧ (True ∨ True)) ∨ ((True ∧ p4) → False)) := by
                  apply Or.inr
                  intro assump_83
                  cases assump_83
                  case intro assump_84 assump_85 =>
                    have assump_231 : (((True ∧ p4) ∧ (True ∨ True)) ∨ ((True ∧ p4) → False)) := by
                      apply Or.inl
                      apply And.intro
                      apply And.intro
                      apply True.intro
                      exact assump_85
                      apply Or.inl
                      apply True.intro
                    let assump_91 := assump_3 assump_231
                    have assump_232 : ((False → p5) → (True ∨ p1)) := by
                      intro assump_93
                      apply Or.inl
                      apply True.intro
                    let assump_92 := assump_91 assump_232
                    apply False.elim assump_92
                let assump_82 := assump_3 assump_230
                have assump_233 : ((False → p5) → (True ∨ p1)) := by
                  intro assump_100
                  apply Or.inl
                  apply True.intro
                let assump_99 := assump_82 assump_233
                apply False.elim assump_99
        case inr assump_9 =>
          cases assump_5
          case inl assump_108 =>
            have assump_234 : (((True ∧ p4) ∧ (True ∨ True)) ∨ ((True ∧ p4) → False)) := by
              apply Or.inr
              intro assump_115
              cases assump_115
              case intro assump_116 assump_117 =>
                have assump_235 : (((True ∧ p4) ∧ (True ∨ True)) ∨ ((True ∧ p4) → False)) := by
                  apply Or.inl
                  apply And.intro
                  apply And.intro
                  apply True.intro
                  exact assump_117
                  apply Or.inl
                  apply True.intro
                let assump_123 := assump_3 assump_235
                have assump_236 : ((False → p5) → (True ∨ p1)) := by
                  intro assump_125
                  apply Or.inl
                  apply True.intro
                let assump_124 := assump_123 assump_236
                apply False.elim assump_124
            let assump_114 := assump_3 assump_234
            have assump_237 : ((False → p5) → (True ∨ p1)) := by
              intro assump_132
              apply Or.inl
              apply True.intro
            let assump_131 := assump_114 assump_237
            apply False.elim assump_131
          case inr assump_109 =>
            cases assump_109
            case intro assump_138 assump_139 =>
              cases assump_138
              case inl assump_140 =>
                have assump_238 : (((True ∧ p4) ∧ (True ∨ True)) ∨ ((True ∧ p4) → False)) := by
                  apply Or.inr
                  intro assump_149
                  cases assump_149
                  case intro assump_150 assump_151 =>
                    have assump_239 : (((True ∧ p4) ∧ (True ∨ True)) ∨ ((True ∧ p4) → False)) := by
                      apply Or.inl
                      apply And.intro
                      apply And.intro
                      apply True.intro
                      exact assump_151
                      apply Or.inl
                      apply True.intro
                    let assump_157 := assump_3 assump_239
                    have assump_240 : ((False → p5) → (True ∨ p1)) := by
                      intro assump_159
                      apply Or.inl
                      apply True.intro
                    let assump_158 := assump_157 assump_240
                    apply False.elim assump_158
                let assump_148 := assump_3 assump_238
                have assump_241 : ((False → p5) → (True ∨ p1)) := by
                  intro assump_166
                  apply Or.inl
                  apply True.intro
                let assump_165 := assump_148 assump_241
                apply False.elim assump_165
              case inr assump_141 =>
                have assump_242 : (((True ∧ p4) ∧ (True ∨ True)) ∨ ((True ∧ p4) → False)) := by
                  apply Or.inr
                  intro assump_179
                  cases assump_179
                  case intro assump_180 assump_181 =>
                    have assump_243 : (((True ∧ p4) ∧ (True ∨ True)) ∨ ((True ∧ p4) → False)) := by
                      apply Or.inl
                      apply And.intro
                      apply And.intro
                      apply True.intro
                      exact assump_181
                      apply Or.inl
                      apply True.intro
                    let assump_187 := assump_3 assump_243
                    have assump_244 : ((False → p5) → (True ∨ p1)) := by
                      intro assump_189
                      apply Or.inl
                      apply True.intro
                    let assump_188 := assump_187 assump_244
                    apply False.elim assump_188
                let assump_178 := assump_3 assump_242
                have assump_245 : ((False → p5) → (True ∨ p1)) := by
                  intro assump_196
                  apply Or.inl
                  apply True.intro
                let assump_195 := assump_178 assump_245
                apply False.elim assump_195
      case inr assump_7 =>
        cases assump_7
        case intro assump_202 assump_203 =>
          cases assump_202
          case inl assump_204 =>
            cases assump_203
            case intro assump_208 assump_209 =>
              apply False.elim assump_209
          case inr assump_205 =>
            cases assump_203
            case intro assump_216 assump_217 =>
              apply False.elim assump_217


variable (p3 p5 p4 p2 p7 p6 : Prop)
theorem file14_33961 : (((((p3 ∨ p3) → (p3 → False)) → False) → False) → ((((False ∨ p2) → (p3 ∨ p5)) → False) → (((p3 ∧ p7) → (p5 ∧ p4)) ∨ ((p7 ∧ p3) ∨ (p2 ∧ p6))))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  apply And.intro
  cases assump_7
  case intro assump_8 assump_9 =>
    have assump_48 : (((p3 ∨ p3) → (p3 → False)) → False) := by
      intro assump_17
      have assump_49 : (p3 ∨ p3) := by
        apply Or.inl
        exact assump_8
      let assump_20 := assump_17 assump_49
      have assump_50 : p3 := by
        exact assump_8
      let assump_21 := assump_20 assump_50
      apply False.elim assump_21
    let assump_16 := assump_1 assump_48
    apply False.elim assump_16
  cases assump_7
  case intro assump_28 assump_29 =>
    have assump_51 : (((p3 ∨ p3) → (p3 → False)) → False) := by
      intro assump_37
      have assump_52 : (p3 ∨ p3) := by
        apply Or.inl
        exact assump_28
      let assump_40 := assump_37 assump_52
      have assump_53 : p3 := by
        exact assump_28
      let assump_41 := assump_40 assump_53
      apply False.elim assump_41
    let assump_36 := assump_1 assump_51
    apply False.elim assump_36


variable (p3 p5 p1 p0 p7 p2 p4 p6 : Prop)
theorem file14_35195 : ((((((p2 ∨ p7) ∨ (p1 ∧ True)) → False) ∨ (((p0 ∨ False) ∧ (p6 → p2)) ∨ ((True → False) ∧ (p0 ∨ p4)))) ∧ ((((p4 → False) ∨ (p0 ∧ p6)) → ((p3 ∨ p3) ∨ (p5 → p5))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_122 : (((p4 → False) ∨ (p0 ∧ p6)) → ((p3 ∨ p3) ∨ (p5 → p5))) := by
        intro assump_11
        cases assump_11
        case inl assump_12 =>
          apply Or.inr
          intro assump_16
          exact assump_16
        case inr assump_13 =>
          cases assump_13
          case intro assump_19 assump_20 =>
            apply Or.inr
            intro assump_25
            exact assump_25
      let assump_10 := assump_3 assump_122
      apply False.elim assump_10
    case inr assump_5 =>
      cases assump_5
      case inl assump_31 =>
        cases assump_31
        case intro assump_33 assump_34 =>
          cases assump_33
          case inl assump_35 =>
            have assump_123 : (((p4 → False) ∨ (p0 ∧ p6)) → ((p3 ∨ p3) ∨ (p5 → p5))) := by
              intro assump_44
              cases assump_44
              case inl assump_45 =>
                apply Or.inr
                intro assump_49
                exact assump_49
              case inr assump_46 =>
                cases assump_46
                case intro assump_52 assump_53 =>
                  apply Or.inr
                  intro assump_58
                  exact assump_58
            let assump_43 := assump_3 assump_123
            apply False.elim assump_43
          case inr assump_36 =>
            apply False.elim assump_36
      case inr assump_32 =>
        cases assump_32
        case intro assump_66 assump_67 =>
          cases assump_67
          case inl assump_70 =>
            have assump_124 : (((p4 → False) ∨ (p0 ∧ p6)) → ((p3 ∨ p3) ∨ (p5 → p5))) := by
              intro assump_77
              cases assump_77
              case inl assump_78 =>
                apply Or.inr
                intro assump_82
                exact assump_82
              case inr assump_79 =>
                cases assump_79
                case intro assump_85 assump_86 =>
                  apply Or.inr
                  intro assump_91
                  exact assump_91
            let assump_76 := assump_3 assump_124
            apply False.elim assump_76
          case inr assump_71 =>
            have assump_125 : (((p4 → False) ∨ (p0 ∧ p6)) → ((p3 ∨ p3) ∨ (p5 → p5))) := by
              intro assump_102
              cases assump_102
              case inl assump_103 =>
                apply Or.inr
                intro assump_107
                exact assump_107
              case inr assump_104 =>
                cases assump_104
                case intro assump_110 assump_111 =>
                  apply Or.inr
                  intro assump_116
                  exact assump_116
            let assump_101 := assump_3 assump_125
            apply False.elim assump_101


variable (p3 p5 p7 p4 p0 p6 p2 p1 : Prop)
theorem file14_38274 : (((((p7 ∨ p3) ∧ (p7 ∧ True)) ∧ ((p4 → p6) ∧ (False ∨ p3))) → (((True → p5) ∧ (p4 → False)) ∧ ((False → False) → (True ∨ p6)))) → ((((p4 → p2) ∨ (p0 → False)) → ((p0 → True) ∨ (p5 ∨ False))) ∨ (((p1 ∧ p3) ∧ (p0 ∨ True)) → False))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case inl assump_5 =>
    apply Or.inl
    intro assump_9
    apply True.intro
  case inr assump_6 =>
    apply Or.inl
    intro assump_12
    apply True.intro


variable (p2 p3 p5 p0 p4 p1 p7 : Prop)
theorem file14_38800 : (((((False → False) ∨ (p7 → True)) → False) → (((p1 ∧ p4) ∧ (p1 ∨ True)) ∨ ((p1 → False) → False))) ∨ ((((p5 ∨ p7) → False) ∨ ((p0 → p3) → (True → False))) ∨ (((True → p2) ∧ (p4 → False)) → False))) := by
  apply Or.inl
  intro assump_1
  apply Or.inr
  intro assump_4
  have assump_15 : ((False → False) ∨ (p7 → True)) := by
    apply Or.inl
    intro assump_9
    apply False.elim assump_9
  let assump_8 := assump_1 assump_15
  apply False.elim assump_8


variable (p1 p6 p4 p2 p7 p0 : Prop)
theorem file14_39317 : (((((p6 ∨ True) ∧ (False → False)) ∨ ((p0 ∧ p6) ∨ (False ∨ True))) ∨ (((True → p7) → (p2 → False)) ∧ ((p1 ∨ p4) ∧ (p6 ∨ p4)))) ∨ ((((p1 ∨ p4) ∧ (p0 ∧ False)) → False) ∨ (((False → False) → False) → False))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply And.intro
  apply Or.inr
  apply True.intro
  intro assump_13
  apply False.elim assump_13


variable (p5 p1 p6 p7 p2 p0 : Prop)
theorem file14_39734 : (((((p0 → False) → False) → ((p7 → p6) → (False → p1))) ∧ (((p2 ∧ p6) → False) ∧ ((True ∨ p5) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_16 : (True ∨ p5) := by
        apply Or.inl
        apply True.intro
      let assump_12 := assump_7 assump_16
      apply False.elim assump_12


variable (p7 p1 p5 p3 p2 p6 : Prop)
theorem file14_40199 : (((((True → False) ∧ (p6 ∨ p3)) ∧ ((p6 ∧ p1) ∧ (p5 ∧ p2))) → False) ∨ ((((p2 → False) ∨ (p1 ∧ False)) → ((p7 → False) ∧ (p7 → p2))) ∧ (((p6 → p6) → (p7 → p7)) → False))) := by
  apply Or.inl
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
          case intro assump_14 assump_15 =>
            cases assump_13
            case intro assump_20 assump_21 =>
              have assump_60 : True := by
                apply True.intro
              let assump_31 := assump_4 assump_60
              apply False.elim assump_31
      case inr assump_9 =>
        cases assump_3
        case intro assump_37 assump_38 =>
          cases assump_37
          case intro assump_39 assump_40 =>
            cases assump_38
            case intro assump_45 assump_46 =>
              have assump_61 : True := by
                apply True.intro
              let assump_56 := assump_4 assump_61
              apply False.elim assump_56


variable (p2 p5 p1 p0 p7 p4 : Prop)
theorem file14_41398 : (((((p0 ∨ True) ∧ (False ∧ p1)) → False) ∨ (((p5 → False) → (p1 ∨ p1)) → False)) ∧ ((((p5 ∧ p2) → False) → ((p0 → False) → (p0 → p2))) → (((p7 ∧ p4) ∨ (False ∧ p1)) ∨ ((True → False) → (p2 → False))))) := by
  apply And.intro
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
  intro assump_18
  apply Or.inr
  intro assump_21
  intro assump_22
  have assump_31 : True := by
    apply True.intro
  let assump_27 := assump_21 assump_31
  apply False.elim assump_27


variable (p0 p2 p3 : Prop)
theorem file14_42204 : (((((p0 → True) → (p2 ∨ p3)) → False) ∧ (((False → False) ∨ (p0 → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : ((False → False) ∨ (p0 → False)) := by
      apply Or.inl
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p4 p3 : Prop)
theorem file14_42620 : ((((((p4 ∧ False) → (p3 ∨ True)) → ((False → False) → False)) → False) → False) → False) := by
  intro assump_15
  have assump_40 : ((((p4 ∧ False) → (p3 ∨ True)) → ((False → False) → False)) → False) := by
    intro assump_19
    have assump_41 : ((p4 ∧ False) → (p3 ∨ True)) := by
      intro assump_23
      cases assump_23
      case intro assump_24 assump_25 =>
        apply False.elim assump_25
    let assump_22 := assump_19 assump_41
    have assump_42 : (False → False) := by
      intro assump_31
      apply False.elim assump_31
    let assump_30 := assump_22 assump_42
    apply False.elim assump_30
  let assump_18 := assump_15 assump_40
  apply False.elim assump_18


variable (p0 p1 p6 p4 p7 p3 p2 p5 : Prop)
theorem file14_43367 : (((((p1 ∧ p6) ∨ (p4 → False)) → False) ∧ (((p0 → False) → False) ∧ ((p3 ∧ p6) → (p1 → False)))) → ((((p4 ∨ True) ∨ (p5 ∨ p7)) ∨ ((p2 ∨ p6) ∧ (True → False))) ∨ (((p4 ∧ p5) → False) ∧ ((p7 → False) ∧ (True ∧ True))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      apply Or.inl
      apply Or.inl
      apply Or.inl
      apply Or.inr
      apply True.intro


variable (p2 p6 p3 p7 : Prop)
theorem file14_43866 : ((((((p3 → p3) ∧ (True → False)) → False) ∨ (((p7 → False) ∨ (p3 → False)) ∨ ((p2 ∧ p6) ∧ (True ∨ True)))) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p3 → p3) ∧ (True → False)) → False) ∨ (((p7 → False) ∨ (p3 → False)) ∨ ((p2 ∧ p6) ∧ (True ∨ True)))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_20 : True := by
        apply True.intro
      let assump_12 := assump_7 assump_20
      apply False.elim assump_12
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p6 p4 p5 p3 p2 p7 p0 : Prop)
theorem file14_44497 : (((((p7 ∧ p4) ∧ (False ∧ p5)) ∧ ((p7 → False) ∧ (p0 ∨ p2))) ∧ (((p3 → False) ∧ (p2 → p6)) → ((True ∨ p4) → False))) → False) := by
  intro assump_35
  cases assump_35
  case intro assump_36 assump_37 =>
    cases assump_36
    case intro assump_38 assump_39 =>
      cases assump_38
      case intro assump_40 assump_41 =>
        cases assump_40
        case intro assump_42 assump_43 =>
          cases assump_41
          case intro assump_48 assump_49 =>
            apply False.elim assump_48


variable (p5 p7 p6 p1 : Prop)
theorem file14_45049 : (((((p5 → False) ∨ (p6 → False)) → False) ∧ (((p7 → True) ∨ (p1 → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_13 : ((p7 → True) ∨ (p1 → False)) := by
      apply Or.inl
      intro assump_9
      apply True.intro
    let assump_8 := assump_3 assump_13
    apply False.elim assump_8


variable (p5 p2 p0 p3 p1 : Prop)
theorem file14_45461 : (((((p0 ∨ p5) → False) ∧ ((True ∧ p0) ∧ (p0 ∨ p1))) → (((p0 ∨ p2) ∧ (False → p3)) ∧ ((p1 → False) → (True → p5)))) ∨ ((((True → False) → False) → ((p0 ∧ True) ∧ (p0 ∨ p1))) → False)) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case inl assump_14 =>
          apply Or.inl
          exact assump_14
        case inr assump_15 =>
          apply Or.inl
          exact assump_9
  intro assump_20
  apply False.elim assump_20
  intro assump_23
  intro assump_24
  cases assump_1
  case intro assump_29 assump_30 =>
    cases assump_30
    case intro assump_33 assump_34 =>
      cases assump_33
      case intro assump_35 assump_36 =>
        cases assump_34
        case inl assump_41 =>
          have assump_59 : (p0 ∨ p5) := by
            apply Or.inl
            exact assump_41
          let assump_47 := assump_29 assump_59
          apply False.elim assump_47
        case inr assump_42 =>
          have assump_60 : (p0 ∨ p5) := by
            apply Or.inl
            exact assump_36
          let assump_55 := assump_29 assump_60
          apply False.elim assump_55


variable (p6 p5 p4 p1 p3 : Prop)
theorem file14_46820 : (((((False ∧ p1) → False) → False) ∨ (((p6 → p1) ∨ (p1 ∧ p1)) ∧ ((p6 → False) ∧ (p5 ∧ p6)))) → ((((p6 ∨ p1) ∨ (False ∨ True)) ∧ ((p4 ∨ p3) ∧ (True → False))) → False)) := by
  intro assump_5
  intro assump_6
  cases assump_6
  case intro assump_7 assump_8 =>
    cases assump_7
    case inl assump_9 =>
      cases assump_9
      case inl assump_11 =>
        cases assump_8
        case intro assump_15 assump_16 =>
          cases assump_15
          case inl assump_17 =>
            cases assump_5
            case inl assump_23 =>
              have assump_401 : ((False ∧ p1) → False) := by
                intro assump_28
                cases assump_28
                case intro assump_29 assump_30 =>
                  apply False.elim assump_29
              let assump_27 := assump_23 assump_401
              apply False.elim assump_27
            case inr assump_24 =>
              cases assump_24
              case intro assump_36 assump_37 =>
                cases assump_36
                case inl assump_38 =>
                  cases assump_37
                  case intro assump_42 assump_43 =>
                    cases assump_43
                    case intro assump_46 assump_47 =>
                      have assump_402 : p6 := by
                        exact assump_47
                      let assump_54 := assump_42 assump_402
                      apply False.elim assump_54
                case inr assump_39 =>
                  cases assump_39
                  case intro assump_58 assump_59 =>
                    cases assump_37
                    case intro assump_64 assump_65 =>
                      cases assump_65
                      case intro assump_68 assump_69 =>
                        have assump_403 : p6 := by
                          exact assump_69
                        let assump_76 := assump_64 assump_403
                        apply False.elim assump_76
          case inr assump_18 =>
            cases assump_5
            case inl assump_84 =>
              have assump_404 : ((False ∧ p1) → False) := by
                intro assump_89
                cases assump_89
                case intro assump_90 assump_91 =>
                  apply False.elim assump_90
              let assump_88 := assump_84 assump_404
              apply False.elim assump_88
            case inr assump_85 =>
              cases assump_85
              case intro assump_97 assump_98 =>
                cases assump_97
                case inl assump_99 =>
                  cases assump_98
                  case intro assump_103 assump_104 =>
                    cases assump_104
                    case intro assump_107 assump_108 =>
                      have assump_405 : p6 := by
                        exact assump_108
                      let assump_115 := assump_103 assump_405
                      apply False.elim assump_115
                case inr assump_100 =>
                  cases assump_100
                  case intro assump_119 assump_120 =>
                    cases assump_98
                    case intro assump_125 assump_126 =>
                      cases assump_126
                      case intro assump_129 assump_130 =>
                        have assump_406 : p6 := by
                          exact assump_130
                        let assump_137 := assump_125 assump_406
                        apply False.elim assump_137
      case inr assump_12 =>
        cases assump_8
        case intro assump_143 assump_144 =>
          cases assump_143
          case inl assump_145 =>
            cases assump_5
            case inl assump_151 =>
              have assump_407 : ((False ∧ p1) → False) := by
                intro assump_156
                cases assump_156
                case intro assump_157 assump_158 =>
                  apply False.elim assump_157
              let assump_155 := assump_151 assump_407
              apply False.elim assump_155
            case inr assump_152 =>
              cases assump_152
              case intro assump_164 assump_165 =>
                cases assump_164
                case inl assump_166 =>
                  cases assump_165
                  case intro assump_170 assump_171 =>
                    cases assump_171
                    case intro assump_174 assump_175 =>
                      have assump_408 : p6 := by
                        exact assump_175
                      let assump_182 := assump_170 assump_408
                      apply False.elim assump_182
                case inr assump_167 =>
                  cases assump_167
                  case intro assump_186 assump_187 =>
                    cases assump_165
                    case intro assump_192 assump_193 =>
                      cases assump_193
                      case intro assump_196 assump_197 =>
                        have assump_409 : p6 := by
                          exact assump_197
                        let assump_204 := assump_192 assump_409
                        apply False.elim assump_204
          case inr assump_146 =>
            cases assump_5
            case inl assump_212 =>
              have assump_410 : ((False ∧ p1) → False) := by
                intro assump_217
                cases assump_217
                case intro assump_218 assump_219 =>
                  apply False.elim assump_218
              let assump_216 := assump_212 assump_410
              apply False.elim assump_216
            case inr assump_213 =>
              cases assump_213
              case intro assump_225 assump_226 =>
                cases assump_225
                case inl assump_227 =>
                  cases assump_226
                  case intro assump_231 assump_232 =>
                    cases assump_232
                    case intro assump_235 assump_236 =>
                      have assump_411 : p6 := by
                        exact assump_236
                      let assump_243 := assump_231 assump_411
                      apply False.elim assump_243
                case inr assump_228 =>
                  cases assump_228
                  case intro assump_247 assump_248 =>
                    cases assump_226
                    case intro assump_253 assump_254 =>
                      cases assump_254
                      case intro assump_257 assump_258 =>
                        have assump_412 : p6 := by
                          exact assump_258
                        let assump_265 := assump_253 assump_412
                        apply False.elim assump_265
    case inr assump_10 =>
      cases assump_10
      case inl assump_269 =>
        apply False.elim assump_269
      case inr assump_270 =>
        cases assump_8
        case intro assump_275 assump_276 =>
          cases assump_275
          case inl assump_277 =>
            cases assump_5
            case inl assump_283 =>
              have assump_413 : ((False ∧ p1) → False) := by
                intro assump_288
                cases assump_288
                case intro assump_289 assump_290 =>
                  apply False.elim assump_289
              let assump_287 := assump_283 assump_413
              apply False.elim assump_287
            case inr assump_284 =>
              cases assump_284
              case intro assump_296 assump_297 =>
                cases assump_296
                case inl assump_298 =>
                  cases assump_297
                  case intro assump_302 assump_303 =>
                    cases assump_303
                    case intro assump_306 assump_307 =>
                      have assump_414 : p6 := by
                        exact assump_307
                      let assump_314 := assump_302 assump_414
                      apply False.elim assump_314
                case inr assump_299 =>
                  cases assump_299
                  case intro assump_318 assump_319 =>
                    cases assump_297
                    case intro assump_324 assump_325 =>
                      cases assump_325
                      case intro assump_328 assump_329 =>
                        have assump_415 : p6 := by
                          exact assump_329
                        let assump_336 := assump_324 assump_415
                        apply False.elim assump_336
          case inr assump_278 =>
            cases assump_5
            case inl assump_344 =>
              have assump_416 : ((False ∧ p1) → False) := by
                intro assump_349
                cases assump_349
                case intro assump_350 assump_351 =>
                  apply False.elim assump_350
              let assump_348 := assump_344 assump_416
              apply False.elim assump_348
            case inr assump_345 =>
              cases assump_345
              case intro assump_357 assump_358 =>
                cases assump_357
                case inl assump_359 =>
                  cases assump_358
                  case intro assump_363 assump_364 =>
                    cases assump_364
                    case intro assump_367 assump_368 =>
                      have assump_417 : p6 := by
                        exact assump_368
                      let assump_375 := assump_363 assump_417
                      apply False.elim assump_375
                case inr assump_360 =>
                  cases assump_360
                  case intro assump_379 assump_380 =>
                    cases assump_358
                    case intro assump_385 assump_386 =>
                      cases assump_386
                      case intro assump_389 assump_390 =>
                        have assump_418 : p6 := by
                          exact assump_390
                        let assump_397 := assump_385 assump_418
                        apply False.elim assump_397


variable (p7 p6 p1 p4 p0 p3 : Prop)
theorem file14_56719 : (((((p0 ∨ True) ∨ (p1 → p3)) ∨ ((p0 ∧ False) → (p4 ∨ p6))) ∨ (((p7 → False) → False) → False)) ∨ ((((p7 → False) → (False → False)) ∨ ((False ∧ p6) ∧ (True ∧ p0))) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inr
  apply True.intro


variable (p2 p0 p5 p6 p1 p7 p4 : Prop)
theorem file14_57056 : (((((p4 ∨ True) → False) → False) ∨ (((p2 → False) ∧ (p1 → False)) → False)) ∨ ((((p6 → p1) → (p1 → p2)) ∨ ((p4 ∨ p2) → (p5 → False))) → (((p4 → p6) → False) ∨ ((p0 ∧ p0) ∨ (False → p7))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  have assump_8 : (p4 ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p6 p2 p4 p3 p1 p5 : Prop)
theorem file14_57497 : (((((p5 ∧ p5) ∨ (p5 → False)) → False) → (((p1 → p1) ∧ (p5 ∧ p3)) ∨ ((p4 → True) ∨ (False ∧ p6)))) ∨ ((((p4 ∨ p2) ∨ (p4 → False)) → ((p3 ∧ p1) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  apply Or.inr
  apply Or.inl
  intro assump_7
  apply True.intro


variable (p6 p3 p1 p0 p7 p5 : Prop)
theorem file14_57824 : ((((((p5 ∨ p1) ∨ (p3 ∧ p7)) ∧ ((p0 → True) ∧ (p6 ∧ False))) → (((False → False) ∨ (p0 → False)) → ((p3 ∧ p3) → (p7 → False)))) → False) → False) := by
  intro assump_1
  have assump_118 : ((((p5 ∨ p1) ∨ (p3 ∧ p7)) ∧ ((p0 → True) ∧ (p6 ∧ False))) → (((False → False) ∨ (p0 → False)) → ((p3 ∧ p3) → (p7 → False)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    cases assump_7
    case intro assump_11 assump_12 =>
      cases assump_6
      case inl assump_17 =>
        cases assump_5
        case intro assump_21 assump_22 =>
          cases assump_21
          case inl assump_23 =>
            cases assump_23
            case inl assump_25 =>
              cases assump_22
              case intro assump_29 assump_30 =>
                cases assump_30
                case intro assump_33 assump_34 =>
                  apply False.elim assump_34
            case inr assump_26 =>
              cases assump_22
              case intro assump_41 assump_42 =>
                cases assump_42
                case intro assump_45 assump_46 =>
                  apply False.elim assump_46
          case inr assump_24 =>
            cases assump_24
            case intro assump_51 assump_52 =>
              cases assump_22
              case intro assump_57 assump_58 =>
                cases assump_58
                case intro assump_61 assump_62 =>
                  apply False.elim assump_62
      case inr assump_18 =>
        cases assump_5
        case intro assump_69 assump_70 =>
          cases assump_69
          case inl assump_71 =>
            cases assump_71
            case inl assump_73 =>
              cases assump_70
              case intro assump_77 assump_78 =>
                cases assump_78
                case intro assump_81 assump_82 =>
                  apply False.elim assump_82
            case inr assump_74 =>
              cases assump_70
              case intro assump_89 assump_90 =>
                cases assump_90
                case intro assump_93 assump_94 =>
                  apply False.elim assump_94
          case inr assump_72 =>
            cases assump_72
            case intro assump_99 assump_100 =>
              cases assump_70
              case intro assump_105 assump_106 =>
                cases assump_106
                case intro assump_109 assump_110 =>
                  apply False.elim assump_110
  let assump_4 := assump_1 assump_118
  apply False.elim assump_4


variable (p1 p6 p4 p2 p0 p7 p3 : Prop)
theorem file14_60369 : (((((p2 ∨ p0) → False) ∧ ((p3 → p7) → False)) → (((True → False) → False) ∨ ((p3 → False) ∨ (p4 ∧ p6)))) ∨ ((((False → False) → (p0 → p1)) → False) ∧ (((p4 ∨ p2) → False) ∧ ((False ∧ p1) ∨ (True ∧ p2))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    intro assump_8
    have assump_15 : True := by
      apply True.intro
    let assump_11 := assump_8 assump_15
    apply False.elim assump_11


variable (p3 : Prop)
theorem file14_60870 : (((((p3 → False) ∧ (True → False)) → False) → False) → False) := by
  intro assump_1
  have assump_19 : (((p3 → False) ∧ (True → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_20 : True := by
        apply True.intro
      let assump_12 := assump_7 assump_20
      apply False.elim assump_12
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p6 p4 p3 p0 p7 : Prop)
theorem file14_61352 : (((((p4 ∨ p0) ∧ (p6 ∨ p3)) ∨ ((p6 ∧ False) → False)) → False) → ((((p7 ∨ p3) → False) → False) → False)) := by
  intro assump_1
  intro assump_2
  have assump_18 : (((p4 ∨ p0) ∧ (p6 ∨ p3)) ∨ ((p6 ∧ False) → False)) := by
    apply Or.inr
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      apply False.elim assump_10
  let assump_7 := assump_1 assump_18
  apply False.elim assump_7


variable (p6 p1 p5 p0 p2 p3 p4 : Prop)
theorem file14_61826 : ((((((False → p1) → (p1 → p3)) ∧ ((True ∨ p2) → (p4 ∧ p5))) → False) ∧ ((((p6 ∧ p4) ∨ (True → False)) ∧ ((p4 → True) ∨ (p4 → p0))) ∧ (((p3 ∧ p5) ∨ (p6 ∧ False)) ∧ ((p3 ∨ p3) ∨ (p5 ∧ p5))))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_7
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_12
        case inl assump_14 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            cases assump_13
            case inl assump_22 =>
              cases assump_11
              case intro assump_26 assump_27 =>
                cases assump_26
                case inl assump_28 =>
                  cases assump_28
                  case intro assump_30 assump_31 =>
                    cases assump_27
                    case inl assump_36 =>
                      cases assump_36
                      case inl assump_38 =>
                        have assump_388 : (((False → p1) → (p1 → p3)) ∧ ((True ∨ p2) → (p4 ∧ p5))) := by
                          apply And.intro
                          intro assump_50
                          intro assump_51
                          exact assump_38
                          intro assump_56
                          apply And.intro
                          cases assump_56
                          case inl assump_57 =>
                            exact assump_17
                          case inr assump_58 =>
                            exact assump_17
                          cases assump_56
                          case inl assump_63 =>
                            exact assump_31
                          case inr assump_64 =>
                            exact assump_31
                        let assump_49 := assump_6 assump_388
                        apply False.elim assump_49
                      case inr assump_39 =>
                        have assump_389 : (((False → p1) → (p1 → p3)) ∧ ((True ∨ p2) → (p4 ∧ p5))) := by
                          apply And.intro
                          intro assump_82
                          intro assump_83
                          exact assump_39
                          intro assump_88
                          apply And.intro
                          cases assump_88
                          case inl assump_89 =>
                            exact assump_17
                          case inr assump_90 =>
                            exact assump_17
                          cases assump_88
                          case inl assump_95 =>
                            exact assump_31
                          case inr assump_96 =>
                            exact assump_31
                        let assump_81 := assump_6 assump_389
                        apply False.elim assump_81
                    case inr assump_37 =>
                      cases assump_37
                      case intro assump_104 assump_105 =>
                        have assump_390 : (((False → p1) → (p1 → p3)) ∧ ((True ∨ p2) → (p4 ∧ p5))) := by
                          apply And.intro
                          intro assump_119
                          intro assump_120
                          exact assump_30
                          intro assump_125
                          apply And.intro
                          cases assump_125
                          case inl assump_126 =>
                            exact assump_17
                          case inr assump_127 =>
                            exact assump_17
                          cases assump_125
                          case inl assump_132 =>
                            exact assump_105
                          case inr assump_133 =>
                            exact assump_105
                        let assump_118 := assump_6 assump_390
                        apply False.elim assump_118
                case inr assump_29 =>
                  cases assump_29
                  case intro assump_141 assump_142 =>
                    apply False.elim assump_142
            case inr assump_23 =>
              cases assump_11
              case intro assump_149 assump_150 =>
                cases assump_149
                case inl assump_151 =>
                  cases assump_151
                  case intro assump_153 assump_154 =>
                    cases assump_150
                    case inl assump_159 =>
                      cases assump_159
                      case inl assump_161 =>
                        have assump_391 : (((False → p1) → (p1 → p3)) ∧ ((True ∨ p2) → (p4 ∧ p5))) := by
                          apply And.intro
                          intro assump_173
                          intro assump_174
                          exact assump_161
                          intro assump_179
                          apply And.intro
                          cases assump_179
                          case inl assump_180 =>
                            exact assump_17
                          case inr assump_181 =>
                            exact assump_17
                          cases assump_179
                          case inl assump_186 =>
                            exact assump_154
                          case inr assump_187 =>
                            exact assump_154
                        let assump_172 := assump_6 assump_391
                        apply False.elim assump_172
                      case inr assump_162 =>
                        have assump_392 : (((False → p1) → (p1 → p3)) ∧ ((True ∨ p2) → (p4 ∧ p5))) := by
                          apply And.intro
                          intro assump_205
                          intro assump_206
                          exact assump_162
                          intro assump_211
                          apply And.intro
                          cases assump_211
                          case inl assump_212 =>
                            exact assump_17
                          case inr assump_213 =>
                            exact assump_17
                          cases assump_211
                          case inl assump_218 =>
                            exact assump_154
                          case inr assump_219 =>
                            exact assump_154
                        let assump_204 := assump_6 assump_392
                        apply False.elim assump_204
                    case inr assump_160 =>
                      cases assump_160
                      case intro assump_227 assump_228 =>
                        have assump_393 : (((False → p1) → (p1 → p3)) ∧ ((True ∨ p2) → (p4 ∧ p5))) := by
                          apply And.intro
                          intro assump_242
                          intro assump_243
                          exact assump_153
                          intro assump_248
                          apply And.intro
                          cases assump_248
                          case inl assump_249 =>
                            exact assump_17
                          case inr assump_250 =>
                            exact assump_17
                          cases assump_248
                          case inl assump_255 =>
                            exact assump_228
                          case inr assump_256 =>
                            exact assump_228
                        let assump_241 := assump_6 assump_393
                        apply False.elim assump_241
                case inr assump_152 =>
                  cases assump_152
                  case intro assump_264 assump_265 =>
                    apply False.elim assump_265
        case inr assump_15 =>
          cases assump_13
          case inl assump_272 =>
            cases assump_11
            case intro assump_276 assump_277 =>
              cases assump_276
              case inl assump_278 =>
                cases assump_278
                case intro assump_280 assump_281 =>
                  cases assump_277
                  case inl assump_286 =>
                    cases assump_286
                    case inl assump_288 =>
                      have assump_394 : True := by
                        apply True.intro
                      let assump_296 := assump_15 assump_394
                      apply False.elim assump_296
                    case inr assump_289 =>
                      have assump_395 : True := by
                        apply True.intro
                      let assump_306 := assump_15 assump_395
                      apply False.elim assump_306
                  case inr assump_287 =>
                    cases assump_287
                    case intro assump_310 assump_311 =>
                      have assump_396 : True := by
                        apply True.intro
                      let assump_321 := assump_15 assump_396
                      apply False.elim assump_321
              case inr assump_279 =>
                cases assump_279
                case intro assump_325 assump_326 =>
                  apply False.elim assump_326
          case inr assump_273 =>
            cases assump_11
            case intro assump_333 assump_334 =>
              cases assump_333
              case inl assump_335 =>
                cases assump_335
                case intro assump_337 assump_338 =>
                  cases assump_334
                  case inl assump_343 =>
                    cases assump_343
                    case inl assump_345 =>
                      have assump_397 : True := by
                        apply True.intro
                      let assump_353 := assump_15 assump_397
                      apply False.elim assump_353
                    case inr assump_346 =>
                      have assump_398 : True := by
                        apply True.intro
                      let assump_363 := assump_15 assump_398
                      apply False.elim assump_363
                  case inr assump_344 =>
                    cases assump_344
                    case intro assump_367 assump_368 =>
                      have assump_399 : True := by
                        apply True.intro
                      let assump_378 := assump_15 assump_399
                      apply False.elim assump_378
              case inr assump_336 =>
                cases assump_336
                case intro assump_382 assump_383 =>
                  apply False.elim assump_383


variable (p5 p6 p4 p0 p2 p1 : Prop)
theorem file14_72395 : (((((False ∨ p4) ∧ (True → False)) → ((p5 ∨ p0) → False)) → False) → ((((p5 → p2) → (p6 → False)) ∧ ((p1 → False) ∨ (p0 → p4))) → (((p6 ∧ p0) → False) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_7
    case inl assump_10 =>
      have assump_100 : (((False ∨ p4) ∧ (True → False)) → ((p5 ∨ p0) → False)) := by
        intro assump_17
        intro assump_18
        cases assump_18
        case inl assump_19 =>
          cases assump_17
          case intro assump_23 assump_24 =>
            cases assump_23
            case inl assump_25 =>
              apply False.elim assump_25
            case inr assump_26 =>
              have assump_101 : True := by
                apply True.intro
              let assump_33 := assump_24 assump_101
              apply False.elim assump_33
        case inr assump_20 =>
          cases assump_17
          case intro assump_39 assump_40 =>
            cases assump_39
            case inl assump_41 =>
              apply False.elim assump_41
            case inr assump_42 =>
              have assump_102 : True := by
                apply True.intro
              let assump_49 := assump_40 assump_102
              apply False.elim assump_49
      let assump_16 := assump_1 assump_100
      apply False.elim assump_16
    case inr assump_11 =>
      have assump_103 : (((False ∨ p4) ∧ (True → False)) → ((p5 ∨ p0) → False)) := by
        intro assump_61
        intro assump_62
        cases assump_62
        case inl assump_63 =>
          cases assump_61
          case intro assump_67 assump_68 =>
            cases assump_67
            case inl assump_69 =>
              apply False.elim assump_69
            case inr assump_70 =>
              have assump_104 : True := by
                apply True.intro
              let assump_77 := assump_68 assump_104
              apply False.elim assump_77
        case inr assump_64 =>
          cases assump_61
          case intro assump_83 assump_84 =>
            cases assump_83
            case inl assump_85 =>
              apply False.elim assump_85
            case inr assump_86 =>
              have assump_105 : True := by
                apply True.intro
              let assump_93 := assump_84 assump_105
              apply False.elim assump_93
      let assump_60 := assump_1 assump_103
      apply False.elim assump_60


variable (p4 p0 p7 p1 p6 : Prop)
theorem file14_74885 : ((((((p4 → p6) → (True → p4)) ∧ ((p1 ∧ True) ∧ (p6 ∧ False))) → (((p0 ∧ False) → False) ∧ ((False → p6) ∧ (p7 ∨ True)))) → False) → False) := by
  intro assump_9
  have assump_45 : ((((p4 → p6) → (True → p4)) ∧ ((p1 ∧ True) ∧ (p6 ∧ False))) → (((p0 ∧ False) → False) ∧ ((False → p6) ∧ (p7 ∨ True)))) := by
    intro assump_13
    apply And.intro
    intro assump_14
    cases assump_14
    case intro assump_15 assump_16 =>
      apply False.elim assump_16
    apply And.intro
    intro assump_21
    apply False.elim assump_21
    cases assump_13
    case intro assump_24 assump_25 =>
      cases assump_25
      case intro assump_28 assump_29 =>
        cases assump_28
        case intro assump_30 assump_31 =>
          cases assump_29
          case intro assump_36 assump_37 =>
            apply False.elim assump_37
  let assump_12 := assump_9 assump_45
  apply False.elim assump_12


variable (p0 p3 p4 p1 : Prop)
theorem file14_75829 : (((((False → False) → False) → ((False → p4) ∧ (False ∨ True))) → False) → ((((True ∨ p0) ∨ (p0 ∨ True)) → ((p1 ∧ p3) ∧ (p0 ∨ p1))) → False)) := by
  intro assump_1
  intro assump_2
  have assump_17 : (((False → False) → False) → ((False → p4) ∧ (False ∨ True))) := by
    intro assump_8
    apply And.intro
    intro assump_9
    apply False.elim assump_9
    apply Or.inr
    apply True.intro
  let assump_7 := assump_1 assump_17
  apply False.elim assump_7


variable (p0 p6 p4 p3 p7 p2 p5 p1 : Prop)
theorem file14_76355 : (((((p7 → p6) ∨ (p3 ∧ p5)) → False) ∧ (((p7 → False) ∧ (p2 → p1)) ∧ ((p2 ∨ p1) ∨ (p2 → p4)))) → ((((p1 ∧ p4) ∨ (p5 ∨ False)) ∧ ((p6 → True) ∨ (p2 → p2))) ∧ (((p0 → p7) ∧ (p1 ∨ p2)) ∧ ((p0 ∧ True) ∧ (p7 → False))))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case inl assump_14 =>
          cases assump_14
          case inl assump_16 =>
            have assump_338 : ((p7 → p6) ∨ (p3 ∧ p5)) := by
              apply Or.inl
              intro assump_25
              have assump_339 : p7 := by
                exact assump_25
              let assump_32 := assump_8 assump_339
              apply False.elim assump_32
            let assump_24 := assump_2 assump_338
            apply False.elim assump_24
          case inr assump_17 =>
            have assump_340 : ((p7 → p6) ∨ (p3 ∧ p5)) := by
              apply Or.inl
              intro assump_45
              have assump_341 : p7 := by
                exact assump_45
              let assump_51 := assump_8 assump_341
              apply False.elim assump_51
            let assump_44 := assump_2 assump_340
            apply False.elim assump_44
        case inr assump_15 =>
          have assump_342 : ((p7 → p6) ∨ (p3 ∧ p5)) := by
            apply Or.inl
            intro assump_64
            have assump_343 : p7 := by
              exact assump_64
            let assump_70 := assump_8 assump_343
            apply False.elim assump_70
          let assump_63 := assump_2 assump_342
          apply False.elim assump_63
  cases assump_1
  case intro assump_77 assump_78 =>
    cases assump_78
    case intro assump_81 assump_82 =>
      cases assump_81
      case intro assump_83 assump_84 =>
        cases assump_82
        case inl assump_89 =>
          cases assump_89
          case inl assump_91 =>
            apply Or.inl
            intro assump_95
            apply True.intro
          case inr assump_92 =>
            apply Or.inl
            intro assump_98
            apply True.intro
        case inr assump_90 =>
          apply Or.inl
          intro assump_101
          apply True.intro
  apply And.intro
  apply And.intro
  intro assump_102
  cases assump_1
  case intro assump_105 assump_106 =>
    cases assump_106
    case intro assump_109 assump_110 =>
      cases assump_109
      case intro assump_111 assump_112 =>
        cases assump_110
        case inl assump_117 =>
          cases assump_117
          case inl assump_119 =>
            have assump_344 : ((p7 → p6) ∨ (p3 ∧ p5)) := by
              apply Or.inl
              intro assump_128
              have assump_345 : p7 := by
                exact assump_128
              let assump_135 := assump_111 assump_345
              apply False.elim assump_135
            let assump_127 := assump_105 assump_344
            apply False.elim assump_127
          case inr assump_120 =>
            have assump_346 : ((p7 → p6) ∨ (p3 ∧ p5)) := by
              apply Or.inl
              intro assump_148
              have assump_347 : p7 := by
                exact assump_148
              let assump_154 := assump_111 assump_347
              apply False.elim assump_154
            let assump_147 := assump_105 assump_346
            apply False.elim assump_147
        case inr assump_118 =>
          have assump_348 : ((p7 → p6) ∨ (p3 ∧ p5)) := by
            apply Or.inl
            intro assump_167
            have assump_349 : p7 := by
              exact assump_167
            let assump_173 := assump_111 assump_349
            apply False.elim assump_173
          let assump_166 := assump_105 assump_348
          apply False.elim assump_166
  cases assump_1
  case intro assump_180 assump_181 =>
    cases assump_181
    case intro assump_184 assump_185 =>
      cases assump_184
      case intro assump_186 assump_187 =>
        cases assump_185
        case inl assump_192 =>
          cases assump_192
          case inl assump_194 =>
            apply Or.inr
            exact assump_194
          case inr assump_195 =>
            apply Or.inl
            exact assump_195
        case inr assump_193 =>
          have assump_350 : ((p7 → p6) ∨ (p3 ∧ p5)) := by
            apply Or.inl
            intro assump_206
            have assump_351 : p7 := by
              exact assump_206
            let assump_212 := assump_186 assump_351
            apply False.elim assump_212
          let assump_205 := assump_180 assump_350
          apply False.elim assump_205
  apply And.intro
  apply And.intro
  cases assump_1
  case intro assump_219 assump_220 =>
    cases assump_220
    case intro assump_223 assump_224 =>
      cases assump_223
      case intro assump_225 assump_226 =>
        cases assump_224
        case inl assump_231 =>
          cases assump_231
          case inl assump_233 =>
            have assump_352 : ((p7 → p6) ∨ (p3 ∧ p5)) := by
              apply Or.inl
              intro assump_242
              have assump_353 : p7 := by
                exact assump_242
              let assump_249 := assump_225 assump_353
              apply False.elim assump_249
            let assump_241 := assump_219 assump_352
            apply False.elim assump_241
          case inr assump_234 =>
            have assump_354 : ((p7 → p6) ∨ (p3 ∧ p5)) := by
              apply Or.inl
              intro assump_262
              have assump_355 : p7 := by
                exact assump_262
              let assump_268 := assump_225 assump_355
              apply False.elim assump_268
            let assump_261 := assump_219 assump_354
            apply False.elim assump_261
        case inr assump_232 =>
          have assump_356 : ((p7 → p6) ∨ (p3 ∧ p5)) := by
            apply Or.inl
            intro assump_281
            have assump_357 : p7 := by
              exact assump_281
            let assump_287 := assump_225 assump_357
            apply False.elim assump_287
          let assump_280 := assump_219 assump_356
          apply False.elim assump_280
  apply True.intro
  intro assump_294
  cases assump_1
  case intro assump_297 assump_298 =>
    cases assump_298
    case intro assump_301 assump_302 =>
      cases assump_301
      case intro assump_303 assump_304 =>
        cases assump_302
        case inl assump_309 =>
          cases assump_309
          case inl assump_311 =>
            have assump_358 : p7 := by
              exact assump_294
            let assump_318 := assump_303 assump_358
            apply False.elim assump_318
          case inr assump_312 =>
            have assump_359 : p7 := by
              exact assump_294
            let assump_326 := assump_303 assump_359
            apply False.elim assump_326
        case inr assump_310 =>
          have assump_360 : p7 := by
            exact assump_294
          let assump_334 := assump_303 assump_360
          apply False.elim assump_334


variable (p4 p1 p3 p7 p5 p2 : Prop)
theorem file14_83472 : (((((p5 → p5) → False) → ((p5 → p2) → (p7 ∧ p1))) → False) → ((((True → p2) ∨ (p7 ∨ p3)) ∨ ((p3 ∧ p4) ∧ (p7 ∧ False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case inl assump_5 =>
      have assump_112 : (((p5 → p5) → False) → ((p5 → p2) → (p7 ∧ p1))) := by
        intro assump_12
        intro assump_13
        apply And.intro
        have assump_113 : (p5 → p5) := by
          intro assump_19
          exact assump_19
        let assump_18 := assump_12 assump_113
        apply False.elim assump_18
        have assump_114 : (p5 → p5) := by
          intro assump_30
          exact assump_30
        let assump_29 := assump_12 assump_114
        apply False.elim assump_29
      let assump_11 := assump_1 assump_112
      apply False.elim assump_11
    case inr assump_6 =>
      cases assump_6
      case inl assump_39 =>
        have assump_115 : (((p5 → p5) → False) → ((p5 → p2) → (p7 ∧ p1))) := by
          intro assump_46
          intro assump_47
          apply And.intro
          exact assump_39
          have assump_116 : (p5 → p5) := by
            intro assump_57
            exact assump_57
          let assump_56 := assump_46 assump_116
          apply False.elim assump_56
        let assump_45 := assump_1 assump_115
        apply False.elim assump_45
      case inr assump_40 =>
        have assump_117 : (((p5 → p5) → False) → ((p5 → p2) → (p7 ∧ p1))) := by
          intro assump_71
          intro assump_72
          apply And.intro
          have assump_118 : (p5 → p5) := by
            intro assump_78
            exact assump_78
          let assump_77 := assump_71 assump_118
          apply False.elim assump_77
          have assump_119 : (p5 → p5) := by
            intro assump_89
            exact assump_89
          let assump_88 := assump_71 assump_119
          apply False.elim assump_88
        let assump_70 := assump_1 assump_117
        apply False.elim assump_70
  case inr assump_4 =>
    cases assump_4
    case intro assump_98 assump_99 =>
      cases assump_98
      case intro assump_100 assump_101 =>
        cases assump_99
        case intro assump_106 assump_107 =>
          apply False.elim assump_107


variable (p7 p0 p3 p1 p2 p6 p4 p5 : Prop)
theorem file14_85776 : (((((p3 → p2) ∧ (p7 → False)) → ((True → False) → (False ∧ p2))) ∧ (((p0 → p4) ∧ (p4 → p7)) → ((p0 ∨ True) ∨ (p5 ∨ p6)))) ∨ ((((p4 → False) ∨ (True → False)) → False) → (((p7 ∨ p1) → (p5 → False)) → False))) := by
  apply Or.inl
  apply And.intro
  intro assump_1
  intro assump_2
  apply And.intro
  cases assump_1
  case intro assump_5 assump_6 =>
    have assump_38 : True := by
      apply True.intro
    let assump_13 := assump_2 assump_38
    apply False.elim assump_13
  cases assump_1
  case intro assump_19 assump_20 =>
    have assump_39 : True := by
      apply True.intro
    let assump_27 := assump_2 assump_39
    apply False.elim assump_27
  intro assump_31
  cases assump_31
  case intro assump_32 assump_33 =>
    apply Or.inl
    apply Or.inr
    apply True.intro


variable (p0 p7 p2 p3 : Prop)
theorem file14_86612 : ((((((p2 ∧ p7) → False) ∧ ((False ∧ p0) ∧ (p3 → False))) → False) → False) → False) := by
  intro assump_5
  have assump_23 : ((((p2 ∧ p7) → False) ∧ ((False ∧ p0) ∧ (p3 → False))) → False) := by
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      cases assump_11
      case intro assump_14 assump_15 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          apply False.elim assump_16
  let assump_8 := assump_5 assump_23
  apply False.elim assump_8


variable (p4 p0 p3 p7 p1 p2 : Prop)
theorem file14_87174 : ((((((p4 → False) → False) ∨ ((p2 ∨ p4) → False)) → (((p7 → False) ∨ (False → False)) ∧ ((p3 ∨ p0) → False))) ∧ ((((False ∨ p1) → (p2 → p7)) ∧ ((True → False) → False)) ∧ (((False ∧ True) ∧ (False → False)) ∧ ((p2 ∧ p1) ∨ (p1 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case intro assump_14 assump_15 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              apply False.elim assump_18


variable (p4 p2 p5 p3 : Prop)
theorem file14_87914 : (((((False → False) ∨ (p4 → False)) ∨ ((p2 → p3) → (p5 → p3))) → False) → False) := by
  intro assump_1
  have assump_11 : (((False → False) ∨ (p4 → False)) ∨ ((p2 → p3) → (p5 → p3))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p7 p5 p3 p1 p6 p2 p0 p4 : Prop)
theorem file14_88318 : (((((p3 → p7) → (p0 ∧ p6)) → False) ∧ (((p2 → False) → (p2 → False)) → ((True ∧ False) → (True ∨ False)))) → ((((p5 ∧ p4) ∨ (True → True)) ∨ ((p1 ∧ p2) → False)) ∨ (((p0 → False) → (p4 → False)) ∧ ((p4 → False) ∨ (p6 → False))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    apply Or.inl
    apply Or.inr
    intro assump_8
    apply True.intro


variable (p0 p4 p1 p3 p2 p6 p7 : Prop)
theorem file14_88776 : (((((p0 ∧ p7) → (False → p3)) → ((False → False) → False)) → (((False → p1) → (p7 → False)) ∨ ((p7 → p2) ∨ (p4 → False)))) ∨ ((((p7 ∨ p2) ∨ (p7 ∨ p1)) → ((p1 → False) ∧ (p0 → False))) ∨ (((p0 → False) → False) ∧ ((p1 → p6) ∨ (p0 → False))))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  have assump_24 : ((p0 ∧ p7) → (False → p3)) := by
    intro assump_13
    intro assump_14
    apply False.elim assump_14
  let assump_12 := assump_1 assump_24
  have assump_25 : (False → False) := by
    intro assump_18
    apply False.elim assump_18
  let assump_17 := assump_12 assump_25
  apply False.elim assump_17


variable (p2 p4 p7 p6 p1 p3 p5 p0 : Prop)
theorem file14_89492 : (((((p0 ∨ p5) ∨ (p5 ∨ p0)) ∧ ((True ∨ p5) → False)) ∨ (((p4 ∨ p7) ∧ (p1 → False)) → ((p3 ∧ p5) → (p2 → p1)))) → ((((p5 → False) ∧ (True ∧ p0)) → ((p3 ∧ p5) → (False → False))) ∧ (((p6 → True) ∧ (False → False)) ∨ ((p6 → False) → (p0 ∧ False))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  intro assump_4
  apply False.elim assump_4
  cases assump_1
  case inl assump_7 =>
    cases assump_7
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        cases assump_11
        case inl assump_13 =>
          apply Or.inl
          apply And.intro
          intro assump_19
          apply True.intro
          intro assump_20
          apply False.elim assump_20
        case inr assump_14 =>
          apply Or.inl
          apply And.intro
          intro assump_27
          apply True.intro
          intro assump_28
          apply False.elim assump_28
      case inr assump_12 =>
        cases assump_12
        case inl assump_31 =>
          apply Or.inl
          apply And.intro
          intro assump_37
          apply True.intro
          intro assump_38
          apply False.elim assump_38
        case inr assump_32 =>
          apply Or.inl
          apply And.intro
          intro assump_45
          apply True.intro
          intro assump_46
          apply False.elim assump_46
  case inr assump_8 =>
    apply Or.inl
    apply And.intro
    intro assump_51
    apply True.intro
    intro assump_52
    apply False.elim assump_52


variable (p2 p6 p7 p3 p4 p1 p0 : Prop)
theorem file14_91074 : (((((True ∨ True) → False) ∨ ((True ∨ p2) → (p6 → p7))) ∧ (((p4 ∧ p0) → (True ∨ p4)) → False)) → ((((False ∨ p1) → False) → ((p0 ∨ p6) ∨ (p3 ∨ p4))) → False)) := by
  intro assump_5
  intro assump_6
  cases assump_5
  case intro assump_9 assump_10 =>
    cases assump_9
    case inl assump_11 =>
      have assump_43 : ((p4 ∧ p0) → (True ∨ p4)) := by
        intro assump_18
        cases assump_18
        case intro assump_19 assump_20 =>
          apply Or.inl
          apply True.intro
      let assump_17 := assump_10 assump_43
      apply False.elim assump_17
    case inr assump_12 =>
      have assump_44 : ((p4 ∧ p0) → (True ∨ p4)) := by
        intro assump_33
        cases assump_33
        case intro assump_34 assump_35 =>
          apply Or.inl
          apply True.intro
      let assump_32 := assump_10 assump_44
      apply False.elim assump_32


variable (p0 p7 p2 p1 p3 p6 p5 : Prop)
theorem file14_92001 : (((((p7 ∧ p0) ∨ (p7 → False)) ∧ ((p5 → True) → False)) → (((False ∨ p7) ∧ (p6 ∧ p2)) → False)) ∨ ((((p1 ∧ p7) → (False → p7)) ∨ ((p7 → True) ∨ (p0 ∧ p1))) → (((p6 ∧ p3) → (p3 → False)) ∧ ((p0 → False) ∧ (p6 ∧ p5))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      apply False.elim assump_5
    case inr assump_6 =>
      cases assump_4
      case intro assump_11 assump_12 =>
        cases assump_1
        case intro assump_17 assump_18 =>
          cases assump_17
          case inl assump_19 =>
            cases assump_19
            case intro assump_21 assump_22 =>
              have assump_43 : (p5 → True) := by
                intro assump_30
                apply True.intro
              let assump_29 := assump_18 assump_43
              apply False.elim assump_29
          case inr assump_20 =>
            have assump_44 : (p5 → True) := by
              intro assump_39
              apply True.intro
            let assump_38 := assump_18 assump_44
            apply False.elim assump_38


variable (p5 p3 p7 p2 : Prop)
theorem file14_93171 : (((((p3 → True) ∨ (p5 → p2)) ∨ ((p5 ∨ p7) ∧ (p5 ∧ False))) → False) → False) := by
  intro assump_37
  have assump_45 : (((p3 → True) ∨ (p5 → p2)) ∨ ((p5 ∨ p7) ∧ (p5 ∧ False))) := by
    apply Or.inl
    apply Or.inl
    intro assump_41
    apply True.intro
  let assump_40 := assump_37 assump_45
  apply False.elim assump_40


variable (p6 p7 p2 p3 p1 p4 p0 p5 : Prop)
theorem file14_93563 : (((((p0 → p0) → (p2 ∧ p6)) → ((p2 → p1) ∨ (p5 ∨ False))) ∧ (((p3 ∨ p7) → (p4 ∧ p3)) ∧ ((p4 → p7) ∧ (p5 ∧ False)))) → ((((p1 ∨ p2) ∧ (p4 ∧ p0)) → False) → (((True ∧ p5) → False) → ((p5 → p7) → False)))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_1
  case intro assump_11 assump_12 =>
    cases assump_12
    case intro assump_15 assump_16 =>
      cases assump_16
      case intro assump_19 assump_20 =>
        cases assump_20
        case intro assump_23 assump_24 =>
          apply False.elim assump_24


variable (p0 p3 p5 p4 p6 p1 p2 : Prop)
theorem file14_94178 : (((((p5 → False) → (p5 → p2)) → False) → (((p4 ∧ p4) → False) ∧ ((p2 ∨ p4) ∧ (p0 → False)))) ∨ ((((p6 ∨ p1) → (p0 ∧ p1)) ∧ ((p6 → False) ∧ (p5 ∨ p0))) ∧ (((p0 → False) → False) → ((p3 ∧ True) → (p1 ∨ p0))))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    have assump_60 : ((p5 → False) → (p5 → p2)) := by
      intro assump_12
      intro assump_13
      have assump_61 : p5 := by
        exact assump_13
      let assump_18 := assump_12 assump_61
      apply False.elim assump_18
    let assump_11 := assump_1 assump_60
    apply False.elim assump_11
  apply And.intro
  have assump_62 : ((p5 → False) → (p5 → p2)) := by
    intro assump_28
    intro assump_29
    have assump_63 : p5 := by
      exact assump_29
    let assump_34 := assump_28 assump_63
    apply False.elim assump_34
  let assump_27 := assump_1 assump_62
  apply False.elim assump_27
  intro assump_41
  have assump_64 : ((p5 → False) → (p5 → p2)) := by
    intro assump_47
    intro assump_48
    have assump_65 : p5 := by
      exact assump_48
    let assump_53 := assump_47 assump_65
    apply False.elim assump_53
  let assump_46 := assump_1 assump_64
  apply False.elim assump_46


variable (p2 p3 p0 p5 p4 p7 p6 : Prop)
theorem file14_95476 : (((((True → True) ∧ (p6 → p3)) → ((False ∧ p4) → (p0 ∨ True))) → False) → ((((p2 ∧ p7) ∧ (p4 ∨ p5)) → False) ∨ (((False → False) → False) → False))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_6
      case inl assump_13 =>
        have assump_45 : (((True → True) ∧ (p6 → p3)) → ((False ∧ p4) → (p0 ∨ True))) := by
          intro assump_21
          intro assump_22
          cases assump_22
          case intro assump_23 assump_24 =>
            apply False.elim assump_23
        let assump_20 := assump_1 assump_45
        apply False.elim assump_20
      case inr assump_14 =>
        have assump_46 : (((True → True) ∧ (p6 → p3)) → ((False ∧ p4) → (p0 ∨ True))) := by
          intro assump_36
          intro assump_37
          cases assump_37
          case intro assump_38 assump_39 =>
            apply False.elim assump_38
        let assump_35 := assump_1 assump_46
        apply False.elim assump_35


variable (p3 p0 p6 p7 p1 p5 : Prop)
theorem file14_96587 : ((((((p1 → p1) ∨ (p5 ∨ p0)) → False) → (((p6 → p3) ∨ (p6 → False)) ∧ ((p7 → p1) ∧ (p3 → False)))) → False) → False) := by
  intro assump_15
  have assump_60 : ((((p1 → p1) ∨ (p5 ∨ p0)) → False) → (((p6 → p3) ∨ (p6 → False)) ∧ ((p7 → p1) ∧ (p3 → False)))) := by
    intro assump_19
    apply And.intro
    apply Or.inl
    intro assump_22
    have assump_61 : ((p1 → p1) ∨ (p5 ∨ p0)) := by
      apply Or.inl
      intro assump_27
      exact assump_27
    let assump_26 := assump_19 assump_61
    apply False.elim assump_26
    apply And.intro
    intro assump_33
    have assump_62 : ((p1 → p1) ∨ (p5 ∨ p0)) := by
      apply Or.inl
      intro assump_39
      exact assump_39
    let assump_38 := assump_19 assump_62
    apply False.elim assump_38
    intro assump_45
    have assump_63 : ((p1 → p1) ∨ (p5 ∨ p0)) := by
      apply Or.inl
      intro assump_51
      exact assump_51
    let assump_50 := assump_19 assump_63
    apply False.elim assump_50
  let assump_18 := assump_15 assump_60
  apply False.elim assump_18


variable (p4 p7 p6 p5 : Prop)
theorem file14_97665 : (((((p5 ∨ False) → False) → False) → (((p5 → False) → False) ∨ ((p5 → True) ∨ (True ∨ p7)))) ∨ ((((p6 → False) → (False → False)) ∧ ((p4 ∧ p6) → False)) → False)) := by
  apply Or.inl
  intro assump_7
  apply Or.inl
  intro assump_10
  have assump_30 : ((p5 ∨ False) → False) := by
    intro assump_15
    cases assump_15
    case inl assump_16 =>
      have assump_31 : p5 := by
        exact assump_16
      let assump_21 := assump_10 assump_31
      apply False.elim assump_21
    case inr assump_17 =>
      apply False.elim assump_17
  let assump_14 := assump_7 assump_30
  apply False.elim assump_14


variable (p1 p7 p6 p5 p0 p4 : Prop)
theorem file14_98331 : (((((p1 → False) → (False ∧ p6)) → ((False → False) → (False → False))) → False) → ((((p1 ∧ p0) ∧ (p5 ∨ True)) → ((p4 ∧ p0) ∧ (True ∧ False))) → (((p7 ∨ False) ∨ (p1 ∨ p7)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_4
    case inl assump_6 =>
      have assump_57 : (((p1 → False) → (False ∧ p6)) → ((False → False) → (False → False))) := by
        intro assump_15
        intro assump_16
        intro assump_17
        apply False.elim assump_17
      let assump_14 := assump_1 assump_57
      apply False.elim assump_14
    case inr assump_7 =>
      apply False.elim assump_7
  case inr assump_5 =>
    cases assump_5
    case inl assump_25 =>
      have assump_58 : (((p1 → False) → (False ∧ p6)) → ((False → False) → (False → False))) := by
        intro assump_34
        intro assump_35
        intro assump_36
        apply False.elim assump_36
      let assump_33 := assump_1 assump_58
      apply False.elim assump_33
    case inr assump_26 =>
      have assump_59 : (((p1 → False) → (False ∧ p6)) → ((False → False) → (False → False))) := by
        intro assump_49
        intro assump_50
        intro assump_51
        apply False.elim assump_51
      let assump_48 := assump_1 assump_59
      apply False.elim assump_48


variable (p2 p3 p4 p1 p0 p6 : Prop)
theorem file14_99710 : (((((p6 ∨ p4) ∨ (p2 ∨ p3)) → ((p3 ∧ True) → (p0 → p3))) ∨ (((p6 ∧ p1) → False) → ((p1 ∨ p6) → False))) ∨ ((((p0 ∧ p2) → False) → ((p4 → False) ∨ (False ∧ p3))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_1
    case inl assump_12 =>
      cases assump_12
      case inl assump_14 =>
        exact assump_6
      case inr assump_15 =>
        exact assump_6
    case inr assump_13 =>
      cases assump_13
      case inl assump_20 =>
        exact assump_6
      case inr assump_21 =>
        exact assump_21


variable (p6 p1 p2 p0 : Prop)
theorem file14_100392 : ((((((p1 → p1) ∨ (p2 → False)) → False) → (((p6 ∧ p0) → False) → False)) → False) → False) := by
  intro assump_14
  have assump_34 : ((((p1 → p1) ∨ (p2 → False)) → False) → (((p6 ∧ p0) → False) → False)) := by
    intro assump_18
    intro assump_19
    have assump_35 : ((p1 → p1) ∨ (p2 → False)) := by
      apply Or.inl
      intro assump_25
      exact assump_25
    let assump_24 := assump_18 assump_35
    apply False.elim assump_24
  let assump_17 := assump_14 assump_34
  apply False.elim assump_17


variable (p6 p7 p0 p3 p2 p5 : Prop)
theorem file14_100960 : (((((p0 ∨ p3) → (p6 → p6)) ∨ ((p7 → False) → (True ∨ p3))) → (((p3 ∧ False) ∧ (p6 ∧ True)) ∨ ((p6 → p3) ∧ (p0 → False)))) → ((((p2 → True) → False) → False) ∨ (((p3 ∧ p2) ∨ (True → False)) ∨ ((p2 ∨ p5) ∨ (p5 ∨ p3))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_12 : (p2 → True) := by
    intro assump_8
    apply True.intro
  let assump_7 := assump_4 assump_12
  apply False.elim assump_7


variable (p0 p1 p6 p2 p7 p4 p5 : Prop)
theorem file14_101438 : (((((p1 ∨ p2) → False) → ((p2 ∨ p6) ∨ (p1 ∨ p5))) → False) → ((((p2 → False) ∧ (False → p1)) ∨ ((p1 ∨ True) ∨ (p2 → False))) ∨ (((p0 → p5) → (p4 ∧ p7)) → ((p1 → False) ∨ (p5 ∨ p5))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply And.intro
  intro assump_4
  have assump_18 : (((p1 ∨ p2) → False) → ((p2 ∨ p6) ∨ (p1 ∨ p5))) := by
    intro assump_9
    apply Or.inl
    apply Or.inl
    exact assump_4
  let assump_8 := assump_1 assump_18
  apply False.elim assump_8
  intro assump_15
  apply False.elim assump_15


variable (p2 p7 p1 p0 p4 p6 p5 : Prop)
theorem file14_102030 : ((((((p0 → p6) → (p1 → True)) ∧ ((False → p7) → False)) → (((p1 ∨ p5) → (p2 ∧ False)) ∨ ((p1 ∨ True) → (p4 → False)))) → False) → False) := by
  intro assump_1
  have assump_60 : ((((p0 → p6) → (p1 → True)) ∧ ((False → p7) → False)) → (((p1 ∨ p5) → (p2 ∧ False)) ∨ ((p1 ∨ True) → (p4 → False)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inl
      intro assump_12
      apply And.intro
      cases assump_12
      case inl assump_13 =>
        have assump_61 : (False → p7) := by
          intro assump_19
          apply False.elim assump_19
        let assump_18 := assump_7 assump_61
        apply False.elim assump_18
      case inr assump_14 =>
        have assump_62 : (False → p7) := by
          intro assump_29
          apply False.elim assump_29
        let assump_28 := assump_7 assump_62
        apply False.elim assump_28
      cases assump_12
      case inl assump_35 =>
        have assump_63 : (False → p7) := by
          intro assump_41
          apply False.elim assump_41
        let assump_40 := assump_7 assump_63
        apply False.elim assump_40
      case inr assump_36 =>
        have assump_64 : (False → p7) := by
          intro assump_51
          apply False.elim assump_51
        let assump_50 := assump_7 assump_64
        apply False.elim assump_50
  let assump_4 := assump_1 assump_60
  apply False.elim assump_4


variable (p3 p4 p7 p2 p1 p0 p6 p5 : Prop)
theorem file14_103500 : (((((True ∨ p3) → False) ∧ ((False ∨ p4) → False)) → (((True ∨ p3) ∨ (p2 ∨ p0)) → ((p5 ∨ False) ∨ (p3 → p4)))) ∨ ((((p6 → False) ∨ (p1 ∧ False)) ∨ ((p6 ∨ p5) ∨ (p7 → p3))) → (((p6 ∨ p3) → (p0 ∧ p4)) → ((p6 ∧ True) ∧ (p4 ∨ True))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_1
      case intro assump_9 assump_10 =>
        apply Or.inr
        intro assump_15
        have assump_77 : (True ∨ p3) := by
          apply Or.inl
          apply True.intro
        let assump_20 := assump_9 assump_77
        apply False.elim assump_20
    case inr assump_6 =>
      cases assump_1
      case intro assump_26 assump_27 =>
        apply Or.inr
        intro assump_32
        have assump_78 : (True ∨ p3) := by
          apply Or.inl
          apply True.intro
        let assump_37 := assump_26 assump_78
        apply False.elim assump_37
  case inr assump_4 =>
    cases assump_4
    case inl assump_41 =>
      cases assump_1
      case intro assump_45 assump_46 =>
        apply Or.inr
        intro assump_51
        have assump_79 : (True ∨ p3) := by
          apply Or.inl
          apply True.intro
        let assump_56 := assump_45 assump_79
        apply False.elim assump_56
    case inr assump_42 =>
      cases assump_1
      case intro assump_62 assump_63 =>
        apply Or.inr
        intro assump_68
        have assump_80 : (True ∨ p3) := by
          apply Or.inl
          apply True.intro
        let assump_73 := assump_62 assump_80
        apply False.elim assump_73


variable (p4 p2 p7 p1 p0 p3 : Prop)
theorem file14_105164 : (((((p1 ∨ p7) ∨ (p4 → False)) → ((False → False) → False)) ∧ (((p7 → False) ∨ (p4 ∨ False)) → False)) → ((((p3 ∧ True) ∨ (True ∨ p2)) ∨ ((False ∨ False) ∨ (p7 ∧ True))) → (((p2 ∨ p0) ∨ (p1 → False)) → ((True ∨ p7) ∧ (False ∨ True))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  apply And.intro
  cases assump_3
  case inl assump_4 =>
    cases assump_4
    case inl assump_6 =>
      cases assump_2
      case inl assump_10 =>
        cases assump_10
        case inl assump_12 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_1
            case intro assump_20 assump_21 =>
              apply Or.inl
              apply True.intro
        case inr assump_13 =>
          cases assump_13
          case inl assump_26 =>
            cases assump_1
            case intro assump_30 assump_31 =>
              apply Or.inl
              apply True.intro
          case inr assump_27 =>
            cases assump_1
            case intro assump_38 assump_39 =>
              apply Or.inl
              apply True.intro
      case inr assump_11 =>
        cases assump_11
        case inl assump_44 =>
          cases assump_44
          case inl assump_46 =>
            apply False.elim assump_46
          case inr assump_47 =>
            apply False.elim assump_47
        case inr assump_45 =>
          cases assump_45
          case intro assump_52 assump_53 =>
            cases assump_1
            case intro assump_58 assump_59 =>
              apply Or.inl
              apply True.intro
    case inr assump_7 =>
      cases assump_2
      case inl assump_66 =>
        cases assump_66
        case inl assump_68 =>
          cases assump_68
          case intro assump_70 assump_71 =>
            cases assump_1
            case intro assump_76 assump_77 =>
              apply Or.inl
              apply True.intro
        case inr assump_69 =>
          cases assump_69
          case inl assump_82 =>
            cases assump_1
            case intro assump_86 assump_87 =>
              apply Or.inl
              apply True.intro
          case inr assump_83 =>
            cases assump_1
            case intro assump_94 assump_95 =>
              apply Or.inl
              apply True.intro
      case inr assump_67 =>
        cases assump_67
        case inl assump_100 =>
          cases assump_100
          case inl assump_102 =>
            apply False.elim assump_102
          case inr assump_103 =>
            apply False.elim assump_103
        case inr assump_101 =>
          cases assump_101
          case intro assump_108 assump_109 =>
            cases assump_1
            case intro assump_114 assump_115 =>
              apply Or.inl
              apply True.intro
  case inr assump_5 =>
    cases assump_2
    case inl assump_122 =>
      cases assump_122
      case inl assump_124 =>
        cases assump_124
        case intro assump_126 assump_127 =>
          cases assump_1
          case intro assump_132 assump_133 =>
            apply Or.inl
            apply True.intro
      case inr assump_125 =>
        cases assump_125
        case inl assump_138 =>
          cases assump_1
          case intro assump_142 assump_143 =>
            apply Or.inl
            apply True.intro
        case inr assump_139 =>
          cases assump_1
          case intro assump_150 assump_151 =>
            apply Or.inl
            apply True.intro
    case inr assump_123 =>
      cases assump_123
      case inl assump_156 =>
        cases assump_156
        case inl assump_158 =>
          apply False.elim assump_158
        case inr assump_159 =>
          apply False.elim assump_159
      case inr assump_157 =>
        cases assump_157
        case intro assump_164 assump_165 =>
          cases assump_1
          case intro assump_170 assump_171 =>
            apply Or.inl
            apply True.intro
  cases assump_3
  case inl assump_176 =>
    cases assump_176
    case inl assump_178 =>
      cases assump_2
      case inl assump_182 =>
        cases assump_182
        case inl assump_184 =>
          cases assump_184
          case intro assump_186 assump_187 =>
            cases assump_1
            case intro assump_192 assump_193 =>
              apply Or.inr
              apply True.intro
        case inr assump_185 =>
          cases assump_185
          case inl assump_198 =>
            cases assump_1
            case intro assump_202 assump_203 =>
              apply Or.inr
              apply True.intro
          case inr assump_199 =>
            cases assump_1
            case intro assump_210 assump_211 =>
              apply Or.inr
              apply True.intro
      case inr assump_183 =>
        cases assump_183
        case inl assump_216 =>
          cases assump_216
          case inl assump_218 =>
            apply False.elim assump_218
          case inr assump_219 =>
            apply False.elim assump_219
        case inr assump_217 =>
          cases assump_217
          case intro assump_224 assump_225 =>
            cases assump_1
            case intro assump_230 assump_231 =>
              apply Or.inr
              apply True.intro
    case inr assump_179 =>
      cases assump_2
      case inl assump_238 =>
        cases assump_238
        case inl assump_240 =>
          cases assump_240
          case intro assump_242 assump_243 =>
            cases assump_1
            case intro assump_248 assump_249 =>
              apply Or.inr
              apply True.intro
        case inr assump_241 =>
          cases assump_241
          case inl assump_254 =>
            cases assump_1
            case intro assump_258 assump_259 =>
              apply Or.inr
              apply True.intro
          case inr assump_255 =>
            cases assump_1
            case intro assump_266 assump_267 =>
              apply Or.inr
              apply True.intro
      case inr assump_239 =>
        cases assump_239
        case inl assump_272 =>
          cases assump_272
          case inl assump_274 =>
            apply False.elim assump_274
          case inr assump_275 =>
            apply False.elim assump_275
        case inr assump_273 =>
          cases assump_273
          case intro assump_280 assump_281 =>
            cases assump_1
            case intro assump_286 assump_287 =>
              apply Or.inr
              apply True.intro
  case inr assump_177 =>
    cases assump_2
    case inl assump_294 =>
      cases assump_294
      case inl assump_296 =>
        cases assump_296
        case intro assump_298 assump_299 =>
          cases assump_1
          case intro assump_304 assump_305 =>
            apply Or.inr
            apply True.intro
      case inr assump_297 =>
        cases assump_297
        case inl assump_310 =>
          cases assump_1
          case intro assump_314 assump_315 =>
            apply Or.inr
            apply True.intro
        case inr assump_311 =>
          cases assump_1
          case intro assump_322 assump_323 =>
            apply Or.inr
            apply True.intro
    case inr assump_295 =>
      cases assump_295
      case inl assump_328 =>
        cases assump_328
        case inl assump_330 =>
          apply False.elim assump_330
        case inr assump_331 =>
          apply False.elim assump_331
      case inr assump_329 =>
        cases assump_329
        case intro assump_336 assump_337 =>
          cases assump_1
          case intro assump_342 assump_343 =>
            apply Or.inr
            apply True.intro


variable (p4 p1 p3 p5 p0 p2 : Prop)
theorem file14_112794 : (((((p0 → False) ∧ (p3 ∧ False)) → False) → False) → ((((p2 → p4) ∧ (p0 → p4)) ∨ ((p1 → p5) ∨ (p1 → False))) ∨ (((False ∨ p3) ∧ (p0 → False)) ∧ ((p3 → False) ∨ (False ∨ p0))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply And.intro
  intro assump_4
  have assump_42 : (((p0 → False) ∧ (p3 ∧ False)) → False) := by
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      cases assump_11
      case intro assump_14 assump_15 =>
        apply False.elim assump_15
  let assump_8 := assump_1 assump_42
  apply False.elim assump_8
  intro assump_23
  have assump_43 : (((p0 → False) ∧ (p3 ∧ False)) → False) := by
    intro assump_28
    cases assump_28
    case intro assump_29 assump_30 =>
      cases assump_30
      case intro assump_33 assump_34 =>
        apply False.elim assump_34
  let assump_27 := assump_1 assump_43
  apply False.elim assump_27


variable (p3 p0 p6 p4 p1 p5 : Prop)
theorem file14_113747 : (((((p0 ∧ False) ∨ (p4 ∧ p6)) → ((p4 ∨ p4) ∨ (p0 → False))) ∧ (((p6 ∨ p3) → (True ∨ p4)) → ((p5 ∧ p1) ∧ (p3 → False)))) → ((((p4 ∨ p0) ∧ (True → False)) → False) ∨ (((p1 ∧ False) → (p3 → False)) ∧ ((p6 → False) ∧ (True ∧ False))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        have assump_29 : True := by
          apply True.intro
        let assump_17 := assump_10 assump_29
        apply False.elim assump_17
      case inr assump_12 =>
        have assump_30 : True := by
          apply True.intro
        let assump_25 := assump_10 assump_30
        apply False.elim assump_25


variable (p2 p0 p6 p5 p7 p3 p1 p4 : Prop)
theorem file14_114574 : (((((p2 ∨ p2) ∧ (p4 ∧ False)) → False) ∨ (((True → p4) → (p1 → p5)) → False)) ∨ ((((False → p0) → (p6 → False)) ∨ ((p4 ∨ p7) → (p7 ∧ p3))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        apply False.elim assump_9
    case inr assump_5 =>
      cases assump_3
      case intro assump_16 assump_17 =>
        apply False.elim assump_17


variable (p7 p6 p5 p0 : Prop)
theorem file14_115139 : ((((((True ∧ True) ∧ (p6 ∧ False)) ∧ ((p6 → p7) → False)) → (((p0 ∨ p6) → False) → ((p5 → False) → (True ∧ p5)))) → False) → False) := by
  intro assump_1
  have assump_31 : ((((True ∧ True) ∧ (p6 ∧ False)) ∧ ((p6 → p7) → False)) → (((p0 ∨ p6) → False) → ((p5 → False) → (True ∧ p5)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    apply And.intro
    apply True.intro
    cases assump_5
    case intro assump_12 assump_13 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          cases assump_15
          case intro assump_22 assump_23 =>
            apply False.elim assump_23
  let assump_4 := assump_1 assump_31
  apply False.elim assump_4


variable (p2 p1 p6 p5 p7 : Prop)
theorem file14_115945 : ((((((p5 ∨ True) ∨ (p7 → False)) ∨ ((p1 ∧ p7) → False)) ∨ (((p2 → False) → (p6 → p6)) → ((p7 → False) ∧ (True ∧ p6)))) ∧ ((((p5 ∧ p2) → False) → ((p5 → False) ∧ (False → False))) ∧ (((False ∨ True) → False) ∧ ((False ∧ False) ∨ (p7 ∨ True))))) → False) := by
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
            cases assump_3
            case intro assump_14 assump_15 =>
              cases assump_15
              case intro assump_18 assump_19 =>
                cases assump_19
                case inl assump_22 =>
                  cases assump_22
                  case intro assump_24 assump_25 =>
                    apply False.elim assump_24
                case inr assump_23 =>
                  cases assump_23
                  case inl assump_28 =>
                    have assump_167 : (False ∨ True) := by
                      apply Or.inr
                      apply True.intro
                    let assump_33 := assump_18 assump_167
                    apply False.elim assump_33
                  case inr assump_29 =>
                    have assump_168 : (False ∨ True) := by
                      apply Or.inr
                      apply True.intro
                    let assump_39 := assump_18 assump_168
                    apply False.elim assump_39
          case inr assump_11 =>
            cases assump_3
            case intro assump_45 assump_46 =>
              cases assump_46
              case intro assump_49 assump_50 =>
                cases assump_50
                case inl assump_53 =>
                  cases assump_53
                  case intro assump_55 assump_56 =>
                    apply False.elim assump_55
                case inr assump_54 =>
                  cases assump_54
                  case inl assump_59 =>
                    have assump_169 : (False ∨ True) := by
                      apply Or.inr
                      apply True.intro
                    let assump_64 := assump_49 assump_169
                    apply False.elim assump_64
                  case inr assump_60 =>
                    have assump_170 : (False ∨ True) := by
                      apply Or.inr
                      apply True.intro
                    let assump_70 := assump_49 assump_170
                    apply False.elim assump_70
        case inr assump_9 =>
          cases assump_3
          case intro assump_76 assump_77 =>
            cases assump_77
            case intro assump_80 assump_81 =>
              cases assump_81
              case inl assump_84 =>
                cases assump_84
                case intro assump_86 assump_87 =>
                  apply False.elim assump_86
              case inr assump_85 =>
                cases assump_85
                case inl assump_90 =>
                  have assump_171 : (False ∨ True) := by
                    apply Or.inr
                    apply True.intro
                  let assump_95 := assump_80 assump_171
                  apply False.elim assump_95
                case inr assump_91 =>
                  have assump_172 : (False ∨ True) := by
                    apply Or.inr
                    apply True.intro
                  let assump_101 := assump_80 assump_172
                  apply False.elim assump_101
      case inr assump_7 =>
        cases assump_3
        case intro assump_107 assump_108 =>
          cases assump_108
          case intro assump_111 assump_112 =>
            cases assump_112
            case inl assump_115 =>
              cases assump_115
              case intro assump_117 assump_118 =>
                apply False.elim assump_117
            case inr assump_116 =>
              cases assump_116
              case inl assump_121 =>
                have assump_173 : (False ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_126 := assump_111 assump_173
                apply False.elim assump_126
              case inr assump_122 =>
                have assump_174 : (False ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_132 := assump_111 assump_174
                apply False.elim assump_132
    case inr assump_5 =>
      cases assump_3
      case intro assump_138 assump_139 =>
        cases assump_139
        case intro assump_142 assump_143 =>
          cases assump_143
          case inl assump_146 =>
            cases assump_146
            case intro assump_148 assump_149 =>
              apply False.elim assump_148
          case inr assump_147 =>
            cases assump_147
            case inl assump_152 =>
              have assump_175 : (False ∨ True) := by
                apply Or.inr
                apply True.intro
              let assump_157 := assump_142 assump_175
              apply False.elim assump_157
            case inr assump_153 =>
              have assump_176 : (False ∨ True) := by
                apply Or.inr
                apply True.intro
              let assump_163 := assump_142 assump_176
              apply False.elim assump_163


variable (p4 p3 p7 p0 p6 p5 p1 : Prop)
theorem file14_121327 : ((((((p6 ∧ p1) → False) → False) ∧ (((p5 → False) ∧ (p0 ∧ p4)) ∧ ((p6 → p4) → False))) ∧ ((((False → False) ∨ (p3 → p7)) → ((p7 → p4) → False)) ∨ (((True ∧ p6) ∨ (p6 ∧ False)) → False))) → False) := by
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
            cases assump_3
            case inl assump_22 =>
              have assump_47 : ((False → False) ∨ (p3 → p7)) := by
                apply Or.inl
                intro assump_27
                apply False.elim assump_27
              let assump_26 := assump_22 assump_47
              have assump_48 : (p7 → p4) := by
                intro assump_31
                exact assump_15
              let assump_30 := assump_26 assump_48
              apply False.elim assump_30
            case inr assump_23 =>
              have assump_49 : (p6 → p4) := by
                intro assump_41
                exact assump_15
              let assump_40 := assump_9 assump_49
              apply False.elim assump_40


variable (p0 p2 p5 p4 p1 p7 p6 p3 : Prop)
theorem file14_122634 : (((((p3 → False) ∨ (p6 ∨ p2)) → False) ∧ (((p0 → False) → (True → True)) → ((p7 ∧ False) ∧ (True → p5)))) → ((((p7 → False) → False) → ((p5 → False) → (p1 → p0))) ∧ (((p4 ∨ p3) → (p7 ∨ p1)) → ((p0 ∨ p2) ∨ (True ∧ p6))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_1
  case intro assump_11 assump_12 =>
    have assump_44 : ((p0 → False) → (True → True)) := by
      intro assump_18
      intro assump_19
      apply True.intro
    let assump_17 := assump_12 assump_44
    let assump_20 := And.left assump_17
    let assump_21 := And.right assump_20
    apply False.elim assump_21
  intro assump_26
  cases assump_1
  case intro assump_29 assump_30 =>
    have assump_45 : ((p0 → False) → (True → True)) := by
      intro assump_36
      intro assump_37
      apply True.intro
    let assump_35 := assump_30 assump_45
    let assump_38 := And.left assump_35
    let assump_39 := And.right assump_38
    apply False.elim assump_39


variable (p4 p7 p6 p3 p0 p5 p2 p1 : Prop)
theorem file14_123693 : (((((p1 ∨ p3) → (False → p1)) ∨ ((p7 → p5) ∨ (True ∧ False))) → (((p0 ∨ p6) ∨ (p1 ∨ True)) ∨ ((p7 ∨ p1) ∧ (p2 ∨ p0)))) ∨ ((((p4 ∧ p4) → (p2 ∨ p6)) ∧ ((p1 ∧ p2) ∨ (p6 ∧ p6))) → (((p4 ∧ p7) → (p0 ∧ p6)) → ((p3 ∨ True) ∨ (p3 → False))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply Or.inr
    apply Or.inr
    apply True.intro
  case inr assump_3 =>
    cases assump_3
    case inl assump_6 =>
      apply Or.inl
      apply Or.inr
      apply Or.inr
      apply True.intro
    case inr assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        apply False.elim assump_11


variable (p0 p2 p3 p6 p7 p5 p4 : Prop)
theorem file14_124409 : ((((((p2 ∨ p2) ∧ (p4 ∨ p7)) ∨ ((p0 → p2) → (p3 → p3))) → False) ∧ ((((False → False) ∧ (True → False)) → ((p0 ∨ p5) ∧ (p5 → False))) → (((p0 ∧ p2) ∨ (False → p6)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_40 : (((False → False) ∧ (True → False)) → ((p0 ∨ p5) ∧ (p5 → False))) := by
      intro assump_9
      apply And.intro
      cases assump_9
      case intro assump_10 assump_11 =>
        have assump_41 : True := by
          apply True.intro
        let assump_16 := assump_11 assump_41
        apply False.elim assump_16
      intro assump_20
      cases assump_9
      case intro assump_23 assump_24 =>
        have assump_42 : True := by
          apply True.intro
        let assump_29 := assump_24 assump_42
        apply False.elim assump_29
    let assump_8 := assump_3 assump_40
    have assump_43 : ((p0 ∧ p2) ∨ (False → p6)) := by
      apply Or.inr
      intro assump_34
      apply False.elim assump_34
    let assump_33 := assump_8 assump_43
    apply False.elim assump_33


variable (p4 p0 p2 p7 p3 : Prop)
theorem file14_125527 : (((((p4 ∧ p2) ∨ (p7 ∨ p0)) → ((p3 ∧ False) → (p0 ∨ False))) → False) → False) := by
  intro assump_1
  have assump_16 : (((p4 ∧ p2) ∨ (p7 ∨ p0)) → ((p3 ∧ False) → (p0 ∨ False))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_8
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p3 p4 p2 p7 p6 p0 : Prop)
theorem file14_125961 : (((((p3 ∨ p4) ∨ (p3 → False)) → False) → False) ∨ ((((p7 → p2) ∧ (False → False)) → False) → (((p2 ∨ p6) → False) → ((p0 ∨ p3) → False)))) := by
  apply Or.inl
  intro assump_1
  have assump_16 : ((p3 ∨ p4) ∨ (p3 → False)) := by
    apply Or.inr
    intro assump_5
    have assump_17 : ((p3 ∨ p4) ∨ (p3 → False)) := by
      apply Or.inl
      apply Or.inl
      exact assump_5
    let assump_9 := assump_1 assump_17
    apply False.elim assump_9
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p0 p6 p3 p2 p7 p5 p1 : Prop)
theorem file14_126536 : (((((p5 → True) → False) ∧ ((p5 → False) → (p1 → False))) ∨ (((p2 → False) → False) ∧ ((p7 → p7) ∧ (p1 → p2)))) → ((((p0 → False) ∧ (p1 ∨ True)) → False) → (((p6 → p5) → (p0 → False)) → ((p3 → p3) ∨ (True → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_1
  case inl assump_8 =>
    cases assump_8
    case intro assump_10 assump_11 =>
      apply Or.inl
      intro assump_16
      exact assump_16
  case inr assump_9 =>
    cases assump_9
    case intro assump_19 assump_20 =>
      cases assump_20
      case intro assump_23 assump_24 =>
        apply Or.inl
        intro assump_29
        exact assump_29


variable (p7 p1 p4 p3 : Prop)
theorem file14_127236 : ((((((p3 → True) → False) ∧ ((p4 ∨ p1) → (p1 → p7))) → False) → False) → False) := by
  intro assump_1
  have assump_21 : ((((p3 → True) → False) ∧ ((p4 ∨ p1) → (p1 → p7))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_22 : (p3 → True) := by
        intro assump_14
        apply True.intro
      let assump_13 := assump_6 assump_22
      apply False.elim assump_13
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p4 p3 p6 p2 p1 p5 : Prop)
theorem file14_127788 : ((((((p4 ∧ p6) ∧ (p3 ∨ p1)) → ((True ∨ p3) ∧ (p6 → False))) → (((True ∨ p1) ∨ (p6 ∨ p4)) → ((p2 ∨ p5) → (p3 → True)))) → False) → False) := by
  intro assump_1
  have assump_12 : ((((p4 ∧ p6) ∧ (p3 ∨ p1)) → ((True ∨ p3) ∧ (p6 → False))) → (((True ∨ p1) ∨ (p6 ∨ p4)) → ((p2 ∨ p5) → (p3 → True)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    apply True.intro
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p7 p3 p1 p4 p2 : Prop)
theorem file14_128309 : (((((p1 ∧ p4) ∨ (p2 → True)) → False) → (((p2 ∨ False) ∧ (p4 ∧ p3)) ∨ ((p2 → False) ∨ (True ∧ p3)))) ∨ ((((p2 → False) ∨ (p4 ∨ p7)) ∨ ((True → False) ∨ (p7 ∧ p2))) ∨ (((p3 ∧ p3) ∨ (p3 ∨ True)) → False))) := by
  apply Or.inl
  intro assump_1
  apply Or.inr
  apply Or.inl
  intro assump_4
  have assump_13 : ((p1 ∧ p4) ∨ (p2 → True)) := by
    apply Or.inr
    intro assump_9
    apply True.intro
  let assump_8 := assump_1 assump_13
  apply False.elim assump_8


variable (p5 p2 p4 p1 p7 : Prop)
theorem file14_128828 : ((((((p2 → p5) ∨ (p4 ∨ p1)) ∧ ((p2 → True) → False)) → (((p5 → False) → (p2 ∨ p2)) → ((p7 ∨ p5) → False))) → False) → False) := by
  intro assump_1
  have assump_87 : ((((p2 → p5) ∨ (p4 ∨ p1)) ∧ ((p2 → True) → False)) → (((p5 → False) → (p2 ∨ p2)) → ((p7 ∨ p5) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_7
    case inl assump_8 =>
      cases assump_5
      case intro assump_14 assump_15 =>
        cases assump_14
        case inl assump_16 =>
          have assump_88 : (p2 → True) := by
            intro assump_23
            apply True.intro
          let assump_22 := assump_15 assump_88
          apply False.elim assump_22
        case inr assump_17 =>
          cases assump_17
          case inl assump_27 =>
            have assump_89 : (p2 → True) := by
              intro assump_34
              apply True.intro
            let assump_33 := assump_15 assump_89
            apply False.elim assump_33
          case inr assump_28 =>
            have assump_90 : (p2 → True) := by
              intro assump_43
              apply True.intro
            let assump_42 := assump_15 assump_90
            apply False.elim assump_42
    case inr assump_9 =>
      cases assump_5
      case intro assump_51 assump_52 =>
        cases assump_51
        case inl assump_53 =>
          have assump_91 : (p2 → True) := by
            intro assump_60
            apply True.intro
          let assump_59 := assump_52 assump_91
          apply False.elim assump_59
        case inr assump_54 =>
          cases assump_54
          case inl assump_64 =>
            have assump_92 : (p2 → True) := by
              intro assump_71
              apply True.intro
            let assump_70 := assump_52 assump_92
            apply False.elim assump_70
          case inr assump_65 =>
            have assump_93 : (p2 → True) := by
              intro assump_80
              apply True.intro
            let assump_79 := assump_52 assump_93
            apply False.elim assump_79
  let assump_4 := assump_1 assump_87
  apply False.elim assump_4


variable (p0 p5 p7 p6 p4 p1 p3 : Prop)
theorem file14_130986 : ((((((True ∧ p0) ∨ (p7 → False)) → ((p5 ∨ p3) ∨ (p1 ∨ p4))) → (((p0 ∧ p6) ∧ (False → p5)) ∨ ((p5 → False) → (p4 → True)))) → False) → False) := by
  intro assump_1
  have assump_13 : ((((True ∧ p0) ∨ (p7 → False)) → ((p5 ∨ p3) ∨ (p1 ∨ p4))) → (((p0 ∧ p6) ∧ (False → p5)) ∨ ((p5 → False) → (p4 → True)))) := by
    intro assump_5
    apply Or.inr
    intro assump_8
    intro assump_9
    apply True.intro
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p3 p5 p2 p0 p1 p7 p4 p6 : Prop)
theorem file14_131522 : (((((p6 ∨ p7) ∧ (p4 ∨ p1)) → False) → (((False ∨ True) → False) → ((p5 → p2) → (True ∨ p6)))) ∨ ((((p4 ∨ p7) ∨ (p5 ∧ p7)) → ((p5 ∨ p7) ∧ (p0 ∧ p1))) ∨ (((p3 ∧ p3) ∧ (p7 → False)) → ((p0 → False) ∨ (p7 → p4))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  apply Or.inl
  apply True.intro


variable (p0 p1 p7 p4 p5 p6 p3 p2 : Prop)
theorem file14_131905 : ((((((p3 ∨ p5) ∨ (p1 ∧ p1)) ∧ ((p7 ∧ True) ∧ (p4 ∧ p0))) ∧ (((p4 → False) → (True ∨ p0)) → False)) ∨ ((((p2 ∧ p0) ∧ (False ∨ p6)) ∧ ((p7 → p5) ∧ (False ∨ False))) ∨ (((p6 ∧ False) → (True → p0)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
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
              case intro assump_16 assump_17 =>
                cases assump_15
                case intro assump_22 assump_23 =>
                  have assump_135 : ((p4 → False) → (True ∨ p0)) := by
                    intro assump_31
                    apply Or.inl
                    apply True.intro
                  let assump_30 := assump_5 assump_135
                  apply False.elim assump_30
          case inr assump_11 =>
            cases assump_7
            case intro assump_39 assump_40 =>
              cases assump_39
              case intro assump_41 assump_42 =>
                cases assump_40
                case intro assump_47 assump_48 =>
                  have assump_136 : ((p4 → False) → (True ∨ p0)) := by
                    intro assump_56
                    apply Or.inl
                    apply True.intro
                  let assump_55 := assump_5 assump_136
                  apply False.elim assump_55
        case inr assump_9 =>
          cases assump_9
          case intro assump_62 assump_63 =>
            cases assump_7
            case intro assump_68 assump_69 =>
              cases assump_68
              case intro assump_70 assump_71 =>
                cases assump_69
                case intro assump_76 assump_77 =>
                  have assump_137 : ((p4 → False) → (True ∨ p0)) := by
                    intro assump_85
                    apply Or.inl
                    apply True.intro
                  let assump_84 := assump_5 assump_137
                  apply False.elim assump_84
  case inr assump_3 =>
    cases assump_3
    case inl assump_91 =>
      cases assump_91
      case intro assump_93 assump_94 =>
        cases assump_93
        case intro assump_95 assump_96 =>
          cases assump_95
          case intro assump_97 assump_98 =>
            cases assump_96
            case inl assump_103 =>
              apply False.elim assump_103
            case inr assump_104 =>
              cases assump_94
              case intro assump_109 assump_110 =>
                cases assump_110
                case inl assump_113 =>
                  apply False.elim assump_113
                case inr assump_114 =>
                  apply False.elim assump_114
    case inr assump_92 =>
      have assump_138 : ((p6 ∧ False) → (True → p0)) := by
        intro assump_122
        intro assump_123
        cases assump_122
        case intro assump_126 assump_127 =>
          apply False.elim assump_127
      let assump_121 := assump_92 assump_138
      apply False.elim assump_121


variable (p3 p6 p5 p1 p2 p4 : Prop)
theorem file14_135136 : (((((p4 ∧ p2) → (p2 ∨ p3)) → False) ∨ (((p3 → False) ∨ (p1 ∧ False)) ∧ ((p3 ∧ p4) → (p2 ∨ p6)))) → ((((False ∧ p2) ∧ (p4 ∨ p5)) ∧ ((p5 ∧ True) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        apply False.elim assump_7


variable (p0 p4 p2 : Prop)
theorem file14_135589 : (((((p4 ∧ False) ∧ (p2 → p0)) → False) → False) → False) := by
  intro assump_1
  have assump_17 : (((p4 ∧ False) ∧ (p2 → p0)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_9
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


