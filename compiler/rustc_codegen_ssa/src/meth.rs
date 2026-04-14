use rustc_middle::bug;
use rustc_middle::ty::{self, GenericArgKind, Ty, TyCtxt};
use tracing::debug;

use crate::traits::*;

#[derive(Copy, Clone, Debug)]
pub(crate) struct VirtualIndex(u64);

impl<'a, 'tcx> VirtualIndex {
    pub(crate) fn from_index(index: usize) -> Self {
        VirtualIndex(index as u64)
    }

    pub(crate) fn get_usize<Bx: BuilderMethods<'a, 'tcx>>(
        self,
        bx: &mut Bx,
        llvtable: Bx::Value,
        ty: Ty<'tcx>,
    ) -> Bx::Value {
        // Load the data pointer from the object.
        debug!("get_int({:?}, {:?})", llvtable, self);

        let llty = bx.type_isize();
        let ptr_size = bx.data_layout().pointer_size();
        let is_relative = bx
            .cx()
            .sess()
            .opts
            .unstable_opts
            .experimental_relative_rust_abi_vtables
            .unwrap_or(false);
        let vtable_byte_offset = if is_relative { self.0 * 4 } else { self.0 * ptr_size.bytes() };

        bx.load_vtable_entry(llvtable, llty, vtable_byte_offset, ty, false, false)
    }
}

/// This takes a valid `self` receiver type and extracts the principal trait
/// ref of the type. Return `None` if there is no principal trait.
pub(crate) fn dyn_trait_in_self<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
) -> Option<ty::ExistentialTraitRef<'tcx>> {
    for arg in ty.peel_refs().walk() {
        if let GenericArgKind::Type(ty) = arg.kind()
            && let ty::Dynamic(data, _) = ty.kind()
        {
            // FIXME(arbitrary_self_types): This is likely broken for receivers which
            // have a "non-self" trait objects as a generic argument.
            return data
                .principal()
                .map(|principal| tcx.instantiate_bound_regions_with_erased(principal));
        }
    }

    bug!("expected a `dyn Trait` ty, found {ty:?}")
}
