use std::cell::RefCell;

use rustc_data_structures::fx::FxHashMap;
use rustc_middle::ty::layout::HasTyCtxt;
use rustc_middle::ty::{self, Instance, Ty, TyCtxt};
use rustc_session::Session;

use super::BackendTypes;

pub trait MiscCodegenMethods<'tcx>: BackendTypes {
    fn vtables(
        &self,
    ) -> &RefCell<FxHashMap<(Ty<'tcx>, Option<ty::ExistentialTraitRef<'tcx>>), Self::Value>>;
    fn apply_vcall_visibility_metadata(
        &self,
        _ty: Ty<'tcx>,
        _poly_trait_ref: Option<ty::ExistentialTraitRef<'tcx>>,
        _vtable: Self::Value,
    ) {
    }

    fn get_vtable(
        &self,
        ty: Ty<'tcx>,
        trait_ref: Option<ty::ExistentialTraitRef<'tcx>>,
    ) -> Self::Value
    where
        Self: HasTyCtxt<'tcx>
            + super::consts::ConstCodegenMethods
            + super::debuginfo::DebugInfoCodegenMethods<'tcx>,
    {
        let tcx = self.tcx();

        // Check the cache.
        if let Some(&val) = self.vtables().borrow().get(&(ty, trait_ref)) {
            return val;
        }

        let vtable_alloc_id = tcx.vtable_allocation((ty, trait_ref));
        let vtable_allocation = tcx.global_alloc(vtable_alloc_id).unwrap_memory();
        let vtable_entries = if let Some(trait_ref) = trait_ref {
            let trait_ref = trait_ref.with_self_ty(tcx, ty);
            let trait_ref = tcx.erase_and_anonymize_regions(trait_ref);
            tcx.vtable_entries(trait_ref)
        } else {
            TyCtxt::COMMON_VTABLE_ENTRIES
        };
        let num_entries = vtable_entries.len();

        let vtable = self.construct_vtable(vtable_allocation, num_entries as u64);

        self.apply_vcall_visibility_metadata(ty, trait_ref, vtable);
        self.create_vtable_debuginfo(ty, trait_ref, vtable);
        self.vtables().borrow_mut().insert((ty, trait_ref), vtable);
        vtable
    }
    fn get_fn(&self, instance: Instance<'tcx>) -> Self::Function;
    fn get_fn_addr(&self, instance: Instance<'tcx>) -> Self::Value;
    fn eh_personality(&self) -> Self::Function;
    fn sess(&self) -> &Session;
    fn set_frame_pointer_type(&self, llfn: Self::Function);
    fn apply_target_cpu_attr(&self, llfn: Self::Function);
    /// Declares the extern "C" main function for the entry point. Returns None if the symbol
    /// already exists.
    fn declare_c_main(&self, fn_type: Self::FunctionSignature) -> Option<Self::Function>;
}
