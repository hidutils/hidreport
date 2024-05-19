use std::path::PathBuf;
use std::io::Write;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // For each hid.bin file in our test/data directory, create one basic test function
    // that attempts to parse that report descriptor
    let datadir: PathBuf = [concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data")].iter().collect();
    let out_dir = std::env::var_os("OUT_DIR").unwrap();
    let dest_path = PathBuf::from(&out_dir).join("test-report-descriptors.rs");
    let mut file = std::fs::File::create(dest_path)?;

    writeln!(file, "use hidreport::*;")?;
    writeln!(file)?;

    std::fs::read_dir(datadir)
        .unwrap()
        .flatten()
        .for_each(|rdesc| {
            let filename = rdesc.file_name().into_string().unwrap();
            let funcname = filename.replace([':', '.', '-'], "_");
            let path = rdesc.path();
            writeln!(file, "
#[test]
#[allow(non_snake_case)]
fn test_{funcname}() {{
    let bytes: Vec<u8> = std::fs::read({path:?}).unwrap();
    if !bytes.is_empty() {{
        ReportDescriptor::try_from(&bytes).expect(&format!(\"Failed to parse {filename}\"));
    }}
}}
").unwrap();
        });

    Ok(())
}
