use std::error::Error;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::{fs, io};

use bincode::enc::write::Writer;
use cairo_vm::cairo_run::{
    cairo_run_program_with_initial_scope, write_encoded_memory, CairoRunConfig, EncodeTraceError,
};
use cairo_vm::types::exec_scope::ExecutionScopes;
use cairo_vm::types::layout::CairoLayoutParams;
use cairo_vm::types::layout_name::LayoutName;
use cairo_vm::types::program::Program;
use cairo_vm::vm::errors::cairo_run_errors::CairoRunError;
use cairo_vm::vm::runners::cairo_runner::CairoRunner;
use cairo_vm::vm::vm_core::VirtualMachine;
use cairo_vm::Felt252;

use cairo_bootloader::bootloaders::load_bootloader;
use cairo_bootloader::tasks::make_bootloader_tasks;
use cairo_bootloader::{
    insert_bootloader_input, BootloaderConfig, BootloaderHintProcessor, BootloaderInput,
    PackedOutput, SimpleBootloaderInput, TaskSpec,
};

fn cairo_run_bootloader_in_proof_mode(
    bootloader_program: &Program,
    tasks: Vec<TaskSpec>,
) -> Result<CairoRunner, CairoRunError> {
    let mut hint_processor = BootloaderHintProcessor::new();

    let cairo_run_config = CairoRunConfig {
        entrypoint: "main",
        trace_enabled: true,
        relocate_mem: true,
        layout: LayoutName::dynamic,
        proof_mode: true,
        secure_run: None,
        disable_trace_padding: false,
        allow_missing_builtins: None,
        dynamic_layout_params: Some(
            CairoLayoutParams::from_file(
                &std::env::var("CARGO_MANIFEST_DIR")
                    .map(PathBuf::from)
                    .unwrap()
                    .join("all_cairo_layout.json"),
            )
            .unwrap(),
        ),
    };

    // Build the bootloader input
    let n_tasks = tasks.len();
    let bootloader_input = BootloaderInput {
        simple_bootloader_input: SimpleBootloaderInput {
            fact_topologies_path: None,
            single_page: false,
            tasks,
        },
        bootloader_config: BootloaderConfig {
            simple_bootloader_program_hash: Felt252::from(0),
            supported_cairo_verifier_program_hashes: vec![],
        },
        packed_outputs: vec![PackedOutput::Plain(vec![]); n_tasks],
    };

    // Note: the method used to set the bootloader input depends on
    // https://github.com/lambdaclass/cairo-vm/pull/1772 and may change depending on review.
    let mut exec_scopes = ExecutionScopes::new();
    insert_bootloader_input(&mut exec_scopes, bootloader_input);

    // Run the bootloader
    cairo_run_program_with_initial_scope(
        &bootloader_program,
        &cairo_run_config,
        &mut hint_processor,
        exec_scopes,
    )
}

pub struct FileWriter {
    buf_writer: io::BufWriter<std::fs::File>,
    bytes_written: usize,
}

impl Writer for FileWriter {
    fn write(&mut self, bytes: &[u8]) -> Result<(), bincode::error::EncodeError> {
        self.buf_writer.write_all(bytes);
        self.bytes_written += bytes.len();

        Ok(())
    }
}

impl FileWriter {
    fn new(buf_writer: io::BufWriter<std::fs::File>) -> Self {
        Self {
            buf_writer,
            bytes_written: 0,
        }
    }

    fn flush(&mut self) -> io::Result<()> {
        self.buf_writer.flush()
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    let bootloader_program = load_bootloader()?;
    let fibonacci_program = include_bytes!("echo.json");
    // let pie = include_bytes!("../173404.zip");

    let tasks = make_bootloader_tasks(&[fibonacci_program], &[])?;

    let mut runner = cairo_run_bootloader_in_proof_mode(&bootloader_program, tasks)?;

    let mut output_buffer = "Program Output:\n".to_string();
    runner.vm.write_output(&mut output_buffer)?;

    let root_artifact_path = std::env::var("CARGO_MANIFEST_DIR").map(PathBuf::from)?;

    let private_input = runner.get_air_private_input();
    println!("{:?}", private_input);

    print!("{output_buffer}");

    let trace_path = root_artifact_path.join("trace.bin");
    let memory_path = root_artifact_path.join("memory.bin");
    let private_input_path = root_artifact_path.join("private_input.json");
    let public_input_path = root_artifact_path.join("public_input.json");

    {
        let json = runner
            .get_air_private_input()
            .to_serializable(
                trace_path.to_string_lossy().to_string(),
                memory_path.to_string_lossy().to_string(),
            )
            .serialize_json()
            .unwrap();

        std::fs::write(private_input_path, json)?;
        let json = runner.get_air_public_input()?.serialize_json()?;
        std::fs::write(public_input_path, json)?;
    }
    // let public_inputs = runner.get_air_public_input().unwrap();

    {
        let relocated_trace = runner.relocated_trace.as_ref().unwrap();

        let trace_file = std::fs::File::create(trace_path)?;
        let mut trace_writer =
            FileWriter::new(io::BufWriter::with_capacity(3 * 1024 * 1024, trace_file));

        write_encoded_trace(relocated_trace, &mut trace_writer)?;
        trace_writer.flush()?;
    }

    {
        let memory_file = std::fs::File::create(memory_path)?;
        let mut memory_writer =
            FileWriter::new(io::BufWriter::with_capacity(5 * 1024 * 1024, memory_file));

        cairo_vm::cairo_run::write_encoded_memory(&runner.relocated_memory, &mut memory_writer)?;
        memory_writer.flush()?;
    }

    Ok(())
}

pub fn write_encoded_trace(
    relocated_trace: &[cairo_vm::vm::trace::trace_entry::RelocatedTraceEntry],
    dest: &mut impl Writer,
) -> Result<(), EncodeTraceError> {
    for (i, entry) in relocated_trace.iter().enumerate() {
        dest.write(&((entry.ap as u64).to_le_bytes()));
        dest.write(&((entry.fp as u64).to_le_bytes()));
        dest.write(&((entry.pc as u64).to_le_bytes()));
    }

    Ok(())
}
