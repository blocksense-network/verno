pub mod venir_communication;
pub mod driver;
pub mod annotations;
pub mod vir_backend;

/// This is the variable name which we assign to the special variable named "result".
/// The special variable "result" can be referred only in `ensures` attributes
/// and its value is the body expression of the function to which the `ensures`
/// attribute is attached to.
/// The leading `%` makes it an illegal identifier which ensures that it won't
/// clash with existing identifiers.
pub const FUNC_RETURN_VAR_NAME: &str = "%return";