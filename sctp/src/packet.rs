use crate::chunk::Chunk;

use crate::chunk::chunk_abort::ChunkAbort;
use crate::chunk::chunk_cookie_ack::ChunkCookieAck;
use crate::chunk::chunk_cookie_echo::ChunkCookieEcho;
use crate::chunk::chunk_error::ChunkError;
use crate::chunk::chunk_forward_tsn::ChunkForwardTsn;
use crate::chunk::chunk_header::*;
use crate::chunk::chunk_heartbeat::ChunkHeartbeat;
use crate::chunk::chunk_init::ChunkInit;
use crate::chunk::chunk_payload_data::ChunkPayloadData;
use crate::chunk::chunk_reconfig::ChunkReconfig;
use crate::chunk::chunk_selective_ack::ChunkSelectiveAck;
use crate::chunk::chunk_shutdown::ChunkShutdown;
use crate::chunk::chunk_shutdown_ack::ChunkShutdownAck;
use crate::chunk::chunk_shutdown_complete::ChunkShutdownComplete;
use crate::chunk::chunk_type::*;
use crate::error::{Error, Result};
use crate::util::*;

use crate::chunk::chunk_unknown::ChunkUnknown;
use bytes::{Buf, BufMut, Bytes, BytesMut};
use std::fmt;

///Packet represents an SCTP packet, defined in https://tools.ietf.org/html/rfc4960#section-3
///An SCTP packet is composed of a common header and chunks.  A chunk
///contains either control information or user data.
///
///
///SCTP Packet Format
/// 0                   1                   2                   3
/// 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
///+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
///|                        Common Header                          |
///+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
///|                          Chunk #1                             |
///+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
///|                           ...                                 |
///+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
///|                          Chunk #n                             |
///+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
///
///
///SCTP Common Header Format
///
/// 0                   1                   2                   3
/// 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
///+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
///|     Source Value Number        |     Destination Value Number |
///+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
///|                      Verification Tag                         |
///+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
///|                           Checksum                            |
///+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#[derive(Default, Debug)]
pub(crate) struct Packet {
    pub(crate) source_port: u16,
    pub(crate) destination_port: u16,
    pub(crate) verification_tag: u32,
    pub(crate) chunks: Vec<Box<dyn Chunk + Send + Sync>>,
}

/// makes packet printable
impl fmt::Display for Packet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut res = format!(
            "Packet:
        source_port: {}
        destination_port: {}
        verification_tag: {}
        ",
            self.source_port, self.destination_port, self.verification_tag,
        );
        for chunk in &self.chunks {
            res += format!("Chunk: {}", chunk).as_str();
        }
        write!(f, "{}", res)
    }
}

pub(crate) const PACKET_HEADER_SIZE: usize = 12;

/// Precompute a CRC lookup table for up to LEVEL steps
const fn crc32_lookup_table<const LEVEL: usize>(poly: u32) -> [[u32; 256]; LEVEL] {
    // compute the crc for one byte by doing the slow bitwise calculation
    const fn crc(value: u8, poly: u32) -> u32 {
        let mut crc = value as u32;
        let mut i = 0;
        while i < 8 {
            let has_lowest_bit = crc & 1;
            crc = (crc >> 1) ^ (has_lowest_bit * poly);
            i += 1;
        }
        crc
    }

    let poly = poly.reverse_bits();
    let mut table = [[0u32; 256]; LEVEL];
    let mut i = 0;
    while i < 256 {
        table[0][i] = crc(i as u8, poly);
        i += 1;
    }

    i = 0;
    while i < 256 {
        let mut level = 1;
        while level < LEVEL {
            let previous_level = table[level - 1][i];
            table[level][i] =
                (table[level - 1][i] >> 8) ^ table[0][(previous_level & 0xFF) as usize];
            level += 1;
        }
        i += 1;
    }
    table
}

/// Precomputed lookup table for up to 16 steps
const ISCSI_TABLE: [[u32; 256]; 16] = crc32_lookup_table(0x1EDC6F41);

//calc the crc one byte at a time
const fn crc(mut crc: u32, data: &[u8]) -> u32 {
    let mut i = 0;
    while i < data.len() {
        let lookup_idx = (crc ^ (data[i] as u32)) & 0xFF;
        crc = (crc >> 8) ^ ISCSI_TABLE[0][lookup_idx as usize];
        i += 1;
    }
    !crc
}

// adapted from https://create.stephan-brumme.com/crc32/#slicing-by-16-overview
// this specific alg was submitted to this author by Bulat Ziganshin
const fn crc_slice_16(mut crc: u32, data: &[u8]) -> u32 {
    let mut i = 0;

    // crc for 16 bytes in one iteration
    while i + 16 < data.len() {
        let first = u32::from_le_bytes([data[i], data[i + 1], data[i + 2], data[i + 3]]);
        let first = first ^ crc;
        i += 4;
        let second = u32::from_le_bytes([data[i], data[i + 1], data[i + 2], data[i + 3]]);
        i += 4;
        let third = u32::from_le_bytes([data[i], data[i + 1], data[i + 2], data[i + 3]]);
        i += 4;
        let fourth = u32::from_le_bytes([data[i], data[i + 1], data[i + 2], data[i + 3]]);
        i += 4;
        crc = ISCSI_TABLE[0][((fourth >> 24) & 0xFF) as usize]
            ^ ISCSI_TABLE[1][((fourth >> 16) & 0xFF) as usize]
            ^ ISCSI_TABLE[2][((fourth >> 8) & 0xFF) as usize]
            ^ ISCSI_TABLE[3][((fourth >> 0) & 0xFF) as usize]
            ^ ISCSI_TABLE[4][((third >> 24) & 0xFF) as usize]
            ^ ISCSI_TABLE[5][((third >> 16) & 0xFF) as usize]
            ^ ISCSI_TABLE[6][((third >> 8) & 0xFF) as usize]
            ^ ISCSI_TABLE[7][((third >> 0) & 0xFF) as usize]
            ^ ISCSI_TABLE[8][((second >> 24) & 0xFF) as usize]
            ^ ISCSI_TABLE[9][((second >> 16) & 0xFF) as usize]
            ^ ISCSI_TABLE[10][((second >> 8) & 0xFF) as usize]
            ^ ISCSI_TABLE[11][((second >> 0) & 0xFF) as usize]
            ^ ISCSI_TABLE[12][((first >> 24) & 0xFF) as usize]
            ^ ISCSI_TABLE[13][((first >> 16) & 0xFF) as usize]
            ^ ISCSI_TABLE[14][((first >> 8) & 0xFF) as usize]
            ^ ISCSI_TABLE[15][((first >> 0) & 0xFF) as usize];
    }
    // crc for the remaining <= 15 bytes
    while i < data.len() {
        let lookup_idx = (crc ^ (data[i] as u32)) & 0xFF;
        crc = (crc >> 8) ^ ISCSI_TABLE[0][lookup_idx as usize];
        i += 1;
    }
    crc
}

//iSCSI CRC32 algorithm parameters {
//    width: 32,
//    poly: 0x1edc6f41,
//    init: 0xffffffff,
//    refin: true,
//    refout: true,
//    xorout: 0xffffffff,
//    check: 0xe3069283,
//    residue: 0xb798b438,
//};

/// Optimized iSCSI CRC32 digester
struct IscsiDigest {
    crc: u32,
}

impl IscsiDigest {
    /// Digest on byte slice all at once
    const fn digest(data: &[u8]) -> u32 {
        !crc_slice_16(0xFFFFFFFF, data)
    }

    /// New digester that can handle multiple slices
    fn new() -> Self {
        Self { crc: 0xFFFFFFFF }
    }

    /// Feed data to this digest
    fn update(&mut self, data: &[u8]) {
        self.crc = crc_slice_16(self.crc, data);
    }

    /// Get the crc for the data that has been fed into the digest
    fn finish(self) -> u32 {
        !self.crc
    }
}

#[test]
fn crc_impl() {
    for x in 0..10000 {
        let d = format!("{x}{x}{x}{x}{x}{x}{x}{x}{x}{x}{x}{x}{x}{x}{x}{x}{x}{x}{x}{x}{x}{x}{x}");

        let mut digest = ISCSI_CRC.digest();
        digest.update(d.as_bytes());
        let their_crc = digest.finalize();
        let mut digest = IscsiDigest::new();
        digest.update(d.as_bytes());
        let my_crc = digest.finish();
        assert_eq!(my_crc, their_crc, "CRC for {d:X?} did not match");

        let b = d.as_bytes();
        let b1 = &b[..b.len() / 2];
        let b2 = &b[b.len() / 2..];
        let mut digest = ISCSI_CRC.digest();
        digest.update(b1);
        digest.update(b2);
        let their_crc2 = digest.finalize();
        let mut digest = IscsiDigest::new();
        digest.update(b1);
        digest.update(b2);
        let my_crc2 = digest.finish();

        assert_eq!(my_crc2, my_crc, "CRC for {d:X?} did not match");
        assert_eq!(my_crc2, their_crc2, "CRC for {d:X?} did not match");
    }
}

#[test]
fn crc_example() {
    let packet = [
        19, 136, 19, 136, 0, 0, 0, 0, 1, 86, 122, 23, 1, 0, 0, 26, 230, 175, 86, 132, 0, 16, 0, 0,
        255, 255, 255, 255, 188, 125, 251, 250, 128, 8, 0, 6, 130, 192, 0, 0,
    ];

    let mut digest = IscsiDigest::new();
    digest.update(&packet[0..8]);
    digest.update(&[0, 0, 0, 0]);
    digest.update(&packet[12..]);
    let recv = digest.finish();

    let packet_with_zeroed_checksum = [
        19, 136, 19, 136, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 26, 230, 175, 86, 132, 0, 16, 0, 0, 255,
        255, 255, 255, 188, 125, 251, 250, 128, 8, 0, 6, 130, 192, 0, 0,
    ];
    let send = IscsiDigest::digest(&packet_with_zeroed_checksum);

    assert_eq!(recv, send);
}

impl Packet {
    pub(crate) fn unmarshal(raw: &Bytes) -> Result<Self> {
        if raw.len() < PACKET_HEADER_SIZE {
            return Err(Error::ErrPacketRawTooSmall);
        }

        let reader = &mut raw.clone();

        let source_port = reader.get_u16();
        let destination_port = reader.get_u16();
        let verification_tag = reader.get_u32();

        #[cfg(not(fuzzing))]
        // only check for checksums when we are not fuzzing. This lets the fuzzer test the code much easier without guessing correct checksums.
        {
            let their_checksum = reader.get_u32_le();
            let mut digest = IscsiDigest::new();
            digest.update(&raw[0..8]);
            digest.update(&[0, 0, 0, 0]);
            digest.update(&raw[12..]);
            let our_checksum = digest.finish();

            if their_checksum != our_checksum {
                return Err(Error::ErrChecksumMismatch);
            }
        }
        let mut chunks = vec![];
        let mut offset = PACKET_HEADER_SIZE;
        loop {
            // Exact match, no more chunks
            if offset == raw.len() {
                break;
            } else if offset + CHUNK_HEADER_SIZE > raw.len() {
                return Err(Error::ErrParseSctpChunkNotEnoughData);
            }

            let ct = ChunkType(raw[offset]);
            let c: Box<dyn Chunk + Send + Sync> = match ct {
                CT_INIT => Box::new(ChunkInit::unmarshal(&raw.slice(offset..))?),
                CT_INIT_ACK => Box::new(ChunkInit::unmarshal(&raw.slice(offset..))?),
                CT_ABORT => Box::new(ChunkAbort::unmarshal(&raw.slice(offset..))?),
                CT_COOKIE_ECHO => Box::new(ChunkCookieEcho::unmarshal(&raw.slice(offset..))?),
                CT_COOKIE_ACK => Box::new(ChunkCookieAck::unmarshal(&raw.slice(offset..))?),
                CT_HEARTBEAT => Box::new(ChunkHeartbeat::unmarshal(&raw.slice(offset..))?),
                CT_PAYLOAD_DATA => Box::new(ChunkPayloadData::unmarshal(&raw.slice(offset..))?),
                CT_SACK => Box::new(ChunkSelectiveAck::unmarshal(&raw.slice(offset..))?),
                CT_RECONFIG => Box::new(ChunkReconfig::unmarshal(&raw.slice(offset..))?),
                CT_FORWARD_TSN => Box::new(ChunkForwardTsn::unmarshal(&raw.slice(offset..))?),
                CT_ERROR => Box::new(ChunkError::unmarshal(&raw.slice(offset..))?),
                CT_SHUTDOWN => Box::new(ChunkShutdown::unmarshal(&raw.slice(offset..))?),
                CT_SHUTDOWN_ACK => Box::new(ChunkShutdownAck::unmarshal(&raw.slice(offset..))?),
                CT_SHUTDOWN_COMPLETE => {
                    Box::new(ChunkShutdownComplete::unmarshal(&raw.slice(offset..))?)
                }
                _ => Box::new(ChunkUnknown::unmarshal(&raw.slice(offset..))?),
            };

            let chunk_value_padding = get_padding_size(c.value_length());
            offset += CHUNK_HEADER_SIZE + c.value_length() + chunk_value_padding;
            chunks.push(c);
        }

        Ok(Packet {
            source_port,
            destination_port,
            verification_tag,
            chunks,
        })
    }

    pub(crate) fn marshal_to(&self, writer: &mut BytesMut) -> Result<usize> {
        // Populate static headers
        // 8-12 is Checksum which will be populated when packet is complete
        writer.put_u16(self.source_port);
        writer.put_u16(self.destination_port);
        writer.put_u32(self.verification_tag);

        // This is where the checksum will be written
        let checksum_pos = writer.len();
        writer.extend_from_slice(&[0, 0, 0, 0]);

        // Populate chunks
        for c in &self.chunks {
            c.marshal_to(writer)?;

            let padding_needed = get_padding_size(writer.len());
            if padding_needed != 0 {
                // padding needed is < 4 because we pad to 4
                writer.extend_from_slice(&[0u8; 16][..padding_needed]);
            }
        }

        let checksum = IscsiDigest::digest(writer.as_ref());

        // Checksum is already in BigEndian
        // Using LittleEndian stops it from being flipped
        let checksum_place = &mut writer[checksum_pos..checksum_pos + 4];
        checksum_place.copy_from_slice(&checksum.to_le_bytes());

        Ok(writer.len())
    }

    pub(crate) fn marshal(&self) -> Result<Bytes> {
        let mut buf = BytesMut::with_capacity(PACKET_HEADER_SIZE);
        self.marshal_to(&mut buf)?;
        Ok(buf.freeze())
    }
}

impl Packet {
    pub(crate) fn check_packet(&self) -> Result<()> {
        // All packets must adhere to these rules

        // This is the SCTP sender's port number.  It can be used by the
        // receiver in combination with the source IP address, the SCTP
        // destination port, and possibly the destination IP address to
        // identify the association to which this packet belongs.  The port
        // number 0 MUST NOT be used.
        if self.source_port == 0 {
            return Err(Error::ErrSctpPacketSourcePortZero);
        }

        // This is the SCTP port number to which this packet is destined.
        // The receiving host will use this port number to de-multiplex the
        // SCTP packet to the correct receiving endpoint/application.  The
        // port number 0 MUST NOT be used.
        if self.destination_port == 0 {
            return Err(Error::ErrSctpPacketDestinationPortZero);
        }

        // Check values on the packet that are specific to a particular chunk type
        for c in &self.chunks {
            if let Some(ci) = c.as_any().downcast_ref::<ChunkInit>() {
                if !ci.is_ack {
                    // An INIT or INIT ACK chunk MUST NOT be bundled with any other chunk.
                    // They MUST be the only chunks present in the SCTP packets that carry
                    // them.
                    if self.chunks.len() != 1 {
                        return Err(Error::ErrInitChunkBundled);
                    }

                    // A packet containing an INIT chunk MUST have a zero Verification
                    // Tag.
                    if self.verification_tag != 0 {
                        return Err(Error::ErrInitChunkVerifyTagNotZero);
                    }
                }
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_packet_unmarshal() -> Result<()> {
        let result = Packet::unmarshal(&Bytes::new());
        assert!(
            result.is_err(),
            "Unmarshal should fail when a packet is too small to be SCTP"
        );

        let header_only = Bytes::from_static(&[
            0x13, 0x88, 0x13, 0x88, 0x00, 0x00, 0x00, 0x00, 0x06, 0xa9, 0x00, 0xe1,
        ]);
        let pkt = Packet::unmarshal(&header_only)?;
        //assert!(result.o(), "Unmarshal failed for SCTP packet with no chunks: {}", result);
        assert_eq!(
            pkt.source_port, 5000,
            "Unmarshal passed for SCTP packet, but got incorrect source port exp: {} act: {}",
            5000, pkt.source_port
        );
        assert_eq!(
            pkt.destination_port, 5000,
            "Unmarshal passed for SCTP packet, but got incorrect destination port exp: {} act: {}",
            5000, pkt.destination_port
        );
        assert_eq!(
            pkt.verification_tag, 0,
            "Unmarshal passed for SCTP packet, but got incorrect verification tag exp: {} act: {}",
            0, pkt.verification_tag
        );

        let raw_chunk = Bytes::from_static(&[
            0x13, 0x88, 0x13, 0x88, 0x00, 0x00, 0x00, 0x00, 0x81, 0x46, 0x9d, 0xfc, 0x01, 0x00,
            0x00, 0x56, 0x55, 0xb9, 0x64, 0xa5, 0x00, 0x02, 0x00, 0x00, 0x04, 0x00, 0x08, 0x00,
            0xe8, 0x6d, 0x10, 0x30, 0xc0, 0x00, 0x00, 0x04, 0x80, 0x08, 0x00, 0x09, 0xc0, 0x0f,
            0xc1, 0x80, 0x82, 0x00, 0x00, 0x00, 0x80, 0x02, 0x00, 0x24, 0x9f, 0xeb, 0xbb, 0x5c,
            0x50, 0xc9, 0xbf, 0x75, 0x9c, 0xb1, 0x2c, 0x57, 0x4f, 0xa4, 0x5a, 0x51, 0xba, 0x60,
            0x17, 0x78, 0x27, 0x94, 0x5c, 0x31, 0xe6, 0x5d, 0x5b, 0x09, 0x47, 0xe2, 0x22, 0x06,
            0x80, 0x04, 0x00, 0x06, 0x00, 0x01, 0x00, 0x00, 0x80, 0x03, 0x00, 0x06, 0x80, 0xc1,
            0x00, 0x00,
        ]);

        Packet::unmarshal(&raw_chunk)?;

        Ok(())
    }

    #[test]
    fn test_packet_marshal() -> Result<()> {
        let header_only = Bytes::from_static(&[
            0x13, 0x88, 0x13, 0x88, 0x00, 0x00, 0x00, 0x00, 0x06, 0xa9, 0x00, 0xe1,
        ]);
        let pkt = Packet::unmarshal(&header_only)?;
        let header_only_marshaled = pkt.marshal()?;
        assert_eq!(header_only, header_only_marshaled, "Unmarshal/Marshaled header only packet did not match \nheaderOnly: {:?} \nheader_only_marshaled {:?}", header_only, header_only_marshaled);

        Ok(())
    }

    /*fn BenchmarkPacketGenerateChecksum(b *testing.B) {
        var data [1024]byte

        for i := 0; i < b.N; i++ {
            _ = generatePacketChecksum(data[:])
        }
    }*/
}
